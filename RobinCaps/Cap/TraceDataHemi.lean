import RobinCaps.ThinDomain.Reflect
import RobinCaps.ThinDomain.H1PQuotient
import RobinCaps.Cap.LowerWeak

/-!
# The `CapTraceData` of the unit hemispherical end cap

`RobinCaps/Cap/LowerWeak.lean` states the cap lemma against an explicit trace interface
`RobinCaps.Cap.CapTraceData C`.  This file **constructs** that interface for the unit
hemispherical end cap `Cap.hemisphere m` (every `m`, in particular `m = 1`) out of the even
reflection trace `RobinCaps.ThinDomain.gammaTrace` of `RobinCaps/ThinDomain/Reflect.lean`,
closing the two gaps that `Reflect.lean` left open: measurability of the sphere trace, and the
fact that `gammaTrace` is only *almost everywhere* additive.

## Contents

1. **Measurability of the sphere trace** (`SphereTrace` section, stated for a general
   dimension `n` and radius `R`).  `traceSphere_congr_th`: the explicit slice-average formula of
   `RobinCaps.Sobolev.Weak.traceSphere` only depends on the radial slices up to null sets.
   `stronglyMeasurable_traceSphere_th`: for jointly measurable data the formula is measurable in
   the direction (a parametric-integral argument through
   `StronglyMeasurable.integral_prod_right'`, with the variable endpoint handled by an
   indicator on the product).  `ae_radial_congr_th`: an a.e. equality on the ball passes to
   almost every radial slice (polar coordinates, `integral_ball_polar_symm`).  Combining them,
   `aestronglyMeasurable_traceSphere_th` replaces `u`, `∇u` by the strongly measurable
   representatives `MemLp.mk`.  `integrable_traceSphere_sq_th` then makes the squared trace
   integrable unconditionally, with the majorant of
   `RobinCaps.Sobolev.Weak.traceSphere_sq_integral_le`.
   `traceSphere_eq_of_continuousOn_th` is the consistency statement
   `RobinCaps.Sobolev.Weak.traceSphere_eq_of_continuous` with the global continuity hypothesis
   weakened to continuity of the radial slices on `[R/2, R]`, which is what the cap supplies.
2. **The closure of the cap body** (`mem_closure_body_th`, `capPt_mem_closure_body_th`): the
   *closed* half ball is contained in `closure ((Cap.hemisphere m).body)` — dilate towards the
   interior point `(-1/2, 0)`.  This is what lets the `ContinuousOn u.toFun (closure C.body)`
   hypothesis of `CapTraceData.trΓ_continuous` feed item 1.
3. `aestronglyMeasurable_gammaTrace_th`, `integrable_gammaTrace_sq_th`, `memLp_gammaTrace_th`,
   `integrable_gammaTrace_mul_th`: the `Γ`-trace is in `L²(σ)`, so products of traces are
   integrable (Cauchy–Schwarz).
4. **A pointwise-linear trace.**  `gammaTrace` is only a.e. additive, while `CapTraceData.trΓ`
   must be additive *pointwise*.  As in `RobinCaps/ThinDomain/TraceOne.lean`, the gap is closed
   by a linear section: `nullGamma_th m` is the subspace of functions of `CapSpace m` vanishing
   `σ`-a.e. on `Γ`, `gammaQ_th` is the (genuinely linear) class of `gammaTraceFun`, and
   `trGamma_th = gammaSection_th ∘ gammaQ_th` is a pointwise-linear representative with
   `trGamma_ae_th : ∀ᵐ w, trGamma_th m u (ofBall m w) = gammaTrace u w`.
5. **The boundary form** `gammaForm_th u v = ∫_{w₀ > 0} (Tr u)(Tr v) dσ`, bilinear
   (`bdGamma_th`), symmetric and nonnegative.
6. **The bridge** `capGammaPair_trGamma_th`: `capGammaPair` of `LowerWeak.lean` — the
   surface-of-revolution integral plus the terminal disk — equals `gammaForm_th`.  The terminal
   disk is degenerate (`hemisphere_theta_zero_th`) and the lateral piece is identified through
   `RobinCaps.ThinDomain.capLateralIntegral_hemisphere_eq`.
7. `gammaForm_self_eq_capBoundary_th`: on representatives continuous up to the boundary the form
   is the honest `RobinCaps.Cap.capBoundary`.
8. `gammaTrace_ae_zero_th`: if `u` vanishes a.e. on the body then so does its weak gradient (a.e.
   uniqueness of weak gradients, `gx_ae_zero_of_mem_nullAEP`), hence the reflected data vanish
   a.e. on the ball and the trace vanishes a.e. on the sphere.
9. `gammaForm_self_le_th`: the trace inequality, with constant `2 · max (4·2^m) (2^m)`, from
   `RobinCaps.ThinDomain.gammaTrace_sq_integral_le`.
10. `capTraceDataHemi_th (m) (hm : 1 ≤ m) : CapTraceData (Cap.hemisphere m)` and
    `capTraceDataHemi_bdΓ_eq_th`, the sphere-integral form of the diagonal.

`1 ≤ m` is needed only for `capLateralIntegral_hemisphere_eq` (items 6 and 7).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Metric Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.Cap

open RobinCaps.Domain RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-! ## 1. Measurability of the sphere trace -/

section SphereTrace

variable {n : ℕ} {R : ℝ}

/-- The sphere trace only depends on the radial slices, up to null sets. -/
theorem traceSphere_congr_th (hR : 0 < R) {v₁ v₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {w : EuclideanSpace ℝ (Fin n)}
    (hv : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), v₁ (r • w) = v₂ (r • w))
    (hgg : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), g₁ (r • w) = g₂ (r • w)) :
    traceSphere R v₁ g₁ w = traceSphere R v₂ g₂ w := by
  have hGae : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (0 : ℝ) R →
      inner ℝ (g₁ (r • w)) w = inner ℝ (g₂ (r • w)) w := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hgg] with r hr hmem
    rw [hr hmem]
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ R := by
    rw [ae_iff]
    simp
  have hII : ∀ p q : ℝ, p ∈ Icc (0 : ℝ) R → q ∈ Icc (0 : ℝ) R →
      (∫ t in p..q, inner ℝ (g₁ (t • w)) w) = ∫ t in p..q, inner ℝ (g₂ (t • w)) w := by
    intro p q hp hq
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hGae, hne] with r hr hrR hmem
    rw [Set.uIoc, mem_Ioc] at hmem
    refine hr ⟨?_, ?_⟩
    · exact lt_of_le_of_lt (le_min hp.1 hq.1) hmem.1
    · exact lt_of_le_of_ne (le_trans hmem.2 (max_le hp.2 hq.2)) hrR
  have haM : ((R / 2 + R) / 2) ∈ Icc (0 : ℝ) R := ⟨by linarith, by linarith⟩
  have hRM : R ∈ Icc (0 : ℝ) R := ⟨by linarith, le_rfl⟩
  have houter : (∫ r in Ioo (R / 2) R,
        (v₁ (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (g₁ (t • w)) w))
      = ∫ r in Ioo (R / 2) R,
        (v₂ (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (g₂ (t • w)) w) := by
    refine integral_congr_ae ?_
    have hvsub : ∀ᵐ r ∂(volume.restrict (Ioo (R / 2) R)), v₁ (r • w) = v₂ (r • w) :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (by linarith) le_rfl) hv
    filter_upwards [hvsub, ae_restrict_mem measurableSet_Ioo] with r hr hmem
    rw [hr, hII _ _ haM ⟨by linarith [hmem.1], le_of_lt hmem.2⟩]
  simp only [traceSphere]
  rw [houter, hII _ _ haM hRM]

/-- **The sphere trace of strongly measurable data is measurable in the direction.** -/
theorem stronglyMeasurable_traceSphere_th {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv : Measurable v) (hgm : Measurable g) :
    StronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      traceSphere R v g (w : EuclideanSpace ℝ (Fin n))) := by
  classical
  have hsmul : Measurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
      p.2 • ((p.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
        EuclideanSpace ℝ (Fin n))) :=
    measurable_snd.smul (measurable_subtype_coe.comp measurable_fst)
  have hH : StronglyMeasurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
      inner ℝ (g (p.2 • ((p.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
        EuclideanSpace ℝ (Fin n))))
        ((p.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))) :=
    ((hgm.comp hsmul).inner (measurable_subtype_coe.comp measurable_fst)).stronglyMeasurable
  have hInd : ∀ S : Set ℝ, StronglyMeasurable
      (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => ∫ t in S,
        inner ℝ (g (t • ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))))
          ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))) :=
    fun S => hH.integral_prod_right' (ν := volume.restrict S)
  have hmeasS : ∀ b : ℝ, MeasurableSet
      {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ | b < z.2 ∧ z.2 ≤ z.1.2} :=
    fun b => (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hmeasS' : ∀ b : ℝ, MeasurableSet
      {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ | z.1.2 < z.2 ∧ z.2 ≤ b} :=
    fun b => (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hG1 : StronglyMeasurable
      (fun z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ =>
        inner ℝ (g (z.2 • ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))))
          ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))) :=
    hH.comp_measurable (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
  have hJ1 : ∀ b : ℝ, StronglyMeasurable
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))) := by
    intro b
    have hF : StronglyMeasurable
        (fun z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))) z.2) := by
      have heq : (fun z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))) z.2)
          = Set.indicator {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2}
            (fun z => inner ℝ (g (z.2 • ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))))
              ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n))) := by
        funext z
        by_cases hz : b < z.2 ∧ z.2 ≤ z.1.2
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc b z.1.2 from hz),
            Set.indicator_of_mem (show z ∈ {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc b z.1.2 from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ |
                b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS b)
    have hEq : (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)))
        = fun q => ∫ y : ℝ, (Ioc b q.2).indicator
          (fun t => inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))))
            ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have hJ2 : ∀ b : ℝ, StronglyMeasurable
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))) := by
    intro b
    have hF : StronglyMeasurable
        (fun z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))) z.2) := by
      have heq : (fun z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))) z.2)
          = Set.indicator {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b}
            (fun z => inner ℝ (g (z.2 • ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))))
              ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n))) := by
        funext z
        by_cases hz : z.1.2 < z.2 ∧ z.2 ≤ b
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc z.1.2 b from hz),
            Set.indicator_of_mem (show z ∈ {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc z.1.2 b from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ) × ℝ |
                z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS' b)
    have hEq : (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)))
        = fun q => ∫ y : ℝ, (Ioc q.2 b).indicator
          (fun t => inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))))
            ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have hinner : StronglyMeasurable
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
        v (q.2 • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)))
          - ∫ t in ((R / 2 + R) / 2)..q.2,
            inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
              EuclideanSpace ℝ (Fin n))))
              ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n))) := by
    have hv' : StronglyMeasurable
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
          v (q.2 • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n)))) := (hv.comp hsmul).stronglyMeasurable
    exact hv'.sub ((hJ1 ((R / 2 + R) / 2)).sub (hJ2 ((R / 2 + R) / 2)))
  have hI1 := hinner.integral_prod_right' (ν := volume.restrict (Ioo (R / 2) R))
  have hI2 := ((hInd (Ioc ((R / 2 + R) / 2) R)).sub (hInd (Ioc R ((R / 2 + R) / 2))))
  exact (hI1.const_mul (2 / R)).add hI2

/-- An almost-everywhere equality on the ball passes to almost every radial slice. -/
theorem ae_radial_congr_th (hn : 1 ≤ n) {α : Type*}
    {f₁ f₂ : EuclideanSpace ℝ (Fin n) → α}
    (h : f₁ =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)] f₂) :
    ∀ᵐ w ∂(sphereMeasure n), ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      f₁ (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)))
        = f₂ (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hne : volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)
      {x | ¬ f₁ x = f₂ x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsup, hNmeas, hN0⟩ := exists_measurable_superset_of_null hne
  have hFmeas : Measurable (N.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hNmeas
  have hFnn : ∀ x, 0 ≤ N.indicator (fun _ => (1 : ℝ)) x := fun x => by
    by_cases hx : x ∈ N
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]
  have hFle : ∀ x, N.indicator (fun _ => (1 : ℝ)) x ≤ 1 := fun x => by
    by_cases hx : x ∈ N
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hFint : IntegrableOn (N.indicator (fun _ => (1 : ℝ)))
      (ball (0 : EuclideanSpace ℝ (Fin n)) R) volume := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hFmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
    exact hFle x
  have hFzero : (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R,
      N.indicator (fun _ => (1 : ℝ)) x) = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hmemN : ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)), x ∉ N := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [hmemN] with x hx
    rw [Set.indicator_of_notMem hx]
    rfl
  have hpolar := integral_ball_polar_symm (m := n) hn hFint
  rw [hFzero] at hpolar
  have hBint := integrable_ball_angular (m := n) hn hFint
  have hnn : 0 ≤ᵐ[sphereMeasure n] fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ∫ r in Ioo (0 : ℝ) R, r ^ (n - 1) *
        N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin n))) := by
    filter_upwards with w
    refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := hr.1
    exact mul_nonneg (by positivity) (hFnn _)
  have hinner0 := (integral_eq_zero_iff_of_nonneg_ae hnn hBint).1 hpolar.symm
  have hwint := ae_integrableOn_weighted (m := n) (R := R) hn hFint
  filter_upwards [hinner0, hwint] with w hw hwi
  have haez : (fun r : ℝ => r ^ (n - 1) *
      N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin n))))
      =ᵐ[volume.restrict (Ioo (0 : ℝ) R)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hwi).1 hw
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hr0 : (0 : ℝ) < r := hr.1
    exact mul_nonneg (by positivity) (hFnn _)
  filter_upwards [haez, ae_restrict_mem measurableSet_Ioo] with r hrz hr
  have hrpos : (0 : ℝ) < r := hr.1
  have hzero : r ^ (n - 1) *
      N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin n))) = 0 := hrz
  have hFz : N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin n))) = 0 := by
    rcases mul_eq_zero.1 hzero with h' | h'
    · exact absurd h' (pow_ne_zero _ (ne_of_gt hrpos))
    · exact h'
  by_contra hcon
  have hmem : r • (w : EuclideanSpace ℝ (Fin n)) ∈ N := hNsup hcon
  rw [Set.indicator_of_mem hmem] at hFz
  exact one_ne_zero hFz

/-- **Measurability of the sphere trace.**  This is the caveat left open by
`RobinCaps/ThinDomain/Reflect.lean`: the trace of an `H¹` element of the ball is almost
everywhere equal to the (genuinely measurable) trace of strongly measurable representatives. -/
theorem aestronglyMeasurable_traceSphere_th (hn : 1 ≤ n) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R)) :
    AEStronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin n))) (sphereMeasure n) := by
  refine ⟨fun w => traceSphere R (u.memL2.1.mk _) (u.grad_memL2.1.mk _)
      ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)),
    stronglyMeasurable_traceSphere_th u.memL2.1.stronglyMeasurable_mk.measurable
      u.grad_memL2.1.stronglyMeasurable_mk.measurable, ?_⟩
  filter_upwards [ae_radial_congr_th (R := R) hn u.memL2.1.ae_eq_mk,
    ae_radial_congr_th (R := R) hn u.grad_memL2.1.ae_eq_mk] with w hw1 hw2
  exact traceSphere_congr_th hR hw1 hw2

/-- **Unconditional integrability of the squared sphere trace.**  The pointwise majorant is the
one of `RobinCaps.Sobolev.Weak.traceSphere_sq_integral_le`; measurability comes from
`aestronglyMeasurable_traceSphere_th`. -/
theorem integrable_traceSphere_sq_th (hn : 1 ≤ n) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R)) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin n))) ^ 2) (sphereMeasure n) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hu2 : IntegrableOn (fun x => u.toFun x ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
    refine (u.memL2.integrable_mul u.memL2).congr (Eventually.of_forall fun x => ?_)
    show u.toFun x * u.toFun x = u.toFun x ^ 2
    rw [pow_two]
  have hg2 : IntegrableOn (fun x => ‖u.grad x‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
    refine (u.grad_memL2.norm.integrable_mul u.grad_memL2.norm).congr
      (Eventually.of_forall fun x => ?_)
    show ‖u.grad x‖ * ‖u.grad x‖ = ‖u.grad x‖ ^ 2
    rw [pow_two]
  have hB1 := integrable_ball_angular hn hu2
  have hB2 := integrable_ball_angular hn hg2
  have hN : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (4 / R) * ((R / 2) ^ (n - 1))⁻¹ * (∫ r in Ioo (0 : ℝ) R,
          r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2)
        + R * ((R / 2) ^ (n - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2) (sphereMeasure n) :=
    (hB1.const_mul _).add (hB2.const_mul _)
  have hptwise : ∀ᵐ w ∂(sphereMeasure n),
      (traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
        EuclideanSpace ℝ (Fin n))) ^ 2
      ≤ (4 / R) * ((R / 2) ^ (n - 1))⁻¹ * (∫ r in Ioo (0 : ℝ) R,
          r ^ (n - 1) * (u.toFun (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n)))) ^ 2)
        + R * ((R / 2) ^ (n - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (n - 1) * ‖u.grad (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n)))‖ ^ 2 := by
    filter_upwards [traceSphere_sq_le hn hR u, ae_integrableOn_weighted (R := R) hn hu2,
      ae_integrableOn_weighted (R := R) hn hg2] with w htr h2 h3
    have hsub : Ioo (R / 2) R ⊆ Ioo (0 : ℝ) R := Ioo_subset_Ioo (by linarith) le_rfl
    have hweight : ∀ r ∈ Ioo (R / 2) R, (1 : ℝ) ≤ ((R / 2) ^ (n - 1))⁻¹ * r ^ (n - 1) := by
      intro r hr
      have hp : (0 : ℝ) < (R / 2) ^ (n - 1) := by positivity
      have h1 : (R / 2) ^ (n - 1) ≤ r ^ (n - 1) := by
        gcongr
        exact hr.1.le
      rw [inv_mul_eq_div, le_div_iff₀ hp, one_mul]
      exact h1
    have hA1 : (∫ r in Ioo (R / 2) R, (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2)
        ≤ ((R / 2) ^ (n - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2 := by
      have hmaj : IntegrableOn (fun r : ℝ => ((R / 2) ^ (n - 1))⁻¹ *
          (r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2))
          (Ioo (R / 2) R) := (h2.mono_set hsub).const_mul _
      have step1 : (∫ r in Ioo (R / 2) R, (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2)
          ≤ ∫ r in Ioo (R / 2) R, ((R / 2) ^ (n - 1))⁻¹ *
            (r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => sq_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hwt := hweight r hr
        calc (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2
            = 1 * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2 := (one_mul _).symm
          _ ≤ (((R / 2) ^ (n - 1))⁻¹ * r ^ (n - 1))
              * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2 :=
            mul_le_mul_of_nonneg_right hwt (sq_nonneg _)
          _ = ((R / 2) ^ (n - 1))⁻¹
              * (r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2) := by ring
      have step2 : (∫ r in Ioo (R / 2) R, ((R / 2) ^ (n - 1))⁻¹ *
            (r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2))
          ≤ ((R / 2) ^ (n - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
            (r ^ (n - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))) ^ 2) := by
        rw [← integral_const_mul]
        refine setIntegral_mono_set (h2.const_mul _) ?_ (HasSubset.Subset.eventuallyLE hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hr0 : (0 : ℝ) < r := hr.1
        positivity
      linarith
    have hA2 : (∫ r in Ioo (R / 2) R,
          (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n))) ^ 2)
        ≤ ((R / 2) ^ (n - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2 := by
      have hwn : ‖(w : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
      have hmaj : IntegrableOn (fun r : ℝ => ((R / 2) ^ (n - 1))⁻¹ *
          (r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2))
          (Ioo (R / 2) R) := (h3.mono_set hsub).const_mul _
      have step1 : (∫ r in Ioo (R / 2) R,
            (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin n))))
              (w : EuclideanSpace ℝ (Fin n))) ^ 2)
          ≤ ∫ r in Ioo (R / 2) R, ((R / 2) ^ (n - 1))⁻¹ *
            (r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => sq_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hcs : |inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n))| ≤ ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ := by
          have := abs_real_inner_le_norm (u.grad (r • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n))
          rwa [hwn, mul_one] at this
        have hsq : (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n))) ^ 2
            ≤ ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
        have hwt := hweight r hr
        calc (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin n))))
                (w : EuclideanSpace ℝ (Fin n))) ^ 2
            ≤ ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2 := hsq
          _ = 1 * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2 := (one_mul _).symm
          _ ≤ (((R / 2) ^ (n - 1))⁻¹ * r ^ (n - 1))
              * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hwt (sq_nonneg _)
          _ = ((R / 2) ^ (n - 1))⁻¹
              * (r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2) := by ring
      have step2 : (∫ r in Ioo (R / 2) R, ((R / 2) ^ (n - 1))⁻¹ *
            (r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2))
          ≤ ((R / 2) ^ (n - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
            (r ^ (n - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin n)))‖ ^ 2) := by
        rw [← integral_const_mul]
        refine setIntegral_mono_set (h3.const_mul _) ?_ (HasSubset.Subset.eventuallyLE hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hr0 : (0 : ℝ) < r := hr.1
        positivity
      linarith
    have h4R : (0 : ℝ) < 4 / R := by positivity
    nlinarith [htr, hA1, hA2, hR.le]
  have hmeas : AEStronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin n))) (sphereMeasure n) :=
    aestronglyMeasurable_traceSphere_th hn hR u
  refine Integrable.mono' hN (hmeas.pow 2) ?_
  filter_upwards [hptwise] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hw

/-- **The trace of a function whose radial slices are continuous on `[R/2, R]` is its
restriction.**  This is `RobinCaps.Sobolev.Weak.traceSphere_eq_of_continuous` with the global
continuity hypothesis weakened to continuity of the radial slices, which is all that the
hemispherical cap provides (its representative is only continuous on the closed cap). -/
theorem traceSphere_eq_of_continuousOn_th (hn : 1 ≤ n) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R))
    (hcont : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ContinuousOn (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin n))))
        (Icc (R / 2) R)) :
    ∀ᵐ w ∂(sphereMeasure n),
      traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))
        = u.toFun (R • ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u.toFun (ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
    u.memL2.integrable one_le_two
  filter_upwards [radialSlice_ae hn hR u, ae_integrableOn_slice (R := R) hn huint,
    ae_integrableOn_slice_inner hn u.grad_memL2] with w hw hwu hwi
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  obtain ⟨c, hc⟩ := ae_eq_const_add_integral hab (hwu _ hhalf) (hwi _ hhalf).1 (hw _ hhalf)
  have hcval : (∫ r in Ioo (R / 2) R,
      (u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))
        - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))) = (R / 2) * c := by
    have hpt : (fun r => u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))
        - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))
        =ᵐ[volume.restrict (Ioo (R / 2) R)] fun _ => c := by
      filter_upwards [hc] with r hr
      rw [hr]
      ring
    rw [integral_congr_ae hpt, setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have htr : traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin n))
      = c + ∫ t in ((R / 2 + R) / 2)..R,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
          (w : EuclideanSpace ℝ (Fin n)) := by
    rw [traceSphere, hcval]
    have h2 : (2 / R) * (R / 2 * c) = c := by field_simp
    rw [h2]
  have hGII : IntervalIntegrable (fun t => inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
      (w : EuclideanSpace ℝ (Fin n))) volume (R / 2) R :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hwi _ hhalf).1
  have hmidmem : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]
    exact ⟨by linarith, by linarith⟩
  have hPcont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
        (w : EuclideanSpace ℝ (Fin n))) (Icc (R / 2) R) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hGII hmidmem
    rwa [uIcc_of_le hab.le] at h
  have hfcont : ContinuousOn (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))
      - (c + ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
          (w : EuclideanSpace ℝ (Fin n)))) (Icc (R / 2) R) :=
    (hcont w).sub (continuousOn_const.add hPcont)
  have hkey : ∀ r ∈ Ioo (R / 2) R, u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))
      - (c + ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
          (w : EuclideanSpace ℝ (Fin n))) = 0 := by
    intro r hr
    by_contra hne
    have hat : ContinuousAt (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))
        - (c + ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))) r :=
      hfcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hnb := hat.eventually (eventually_ne_nhds hne)
    have hnbd : {x : ℝ | (u.toFun (x • (w : EuclideanSpace ℝ (Fin n)))
        - (c + ∫ t in ((R / 2 + R) / 2)..x,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))) ≠ 0} ∩ Ioo (R / 2) R ∈ 𝓝 r :=
      inter_mem hnb (Ioo_mem_nhds hr.1 hr.2)
    have hpos : 0 < volume ({x : ℝ | (u.toFun (x • (w : EuclideanSpace ℝ (Fin n)))
        - (c + ∫ t in ((R / 2 + R) / 2)..x,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))) ≠ 0} ∩ Ioo (R / 2) R) :=
      MeasureTheory.Measure.measure_pos_of_mem_nhds volume hnbd
    have hnull : volume ({x : ℝ | (u.toFun (x • (w : EuclideanSpace ℝ (Fin n)))
        - (c + ∫ t in ((R / 2 + R) / 2)..x,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))) ≠ 0} ∩ Ioo (R / 2) R) = 0 := by
      have hc' : ∀ᵐ x ∂volume, x ∈ Ioo (R / 2) R →
          u.toFun (x • (w : EuclideanSpace ℝ (Fin n)))
            = c + ∫ t in ((R / 2 + R) / 2)..x,
              inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
                (w : EuclideanSpace ℝ (Fin n)) :=
        (ae_restrict_iff' measurableSet_Ioo).1 hc
      refine measure_mono_null (fun x hx => ?_) hc'
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff] at hx ⊢
      intro hcon
      exact hx.1 (by rw [hcon hx.2]; ring)
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  have hfR : u.toFun (R • (w : EuclideanSpace ℝ (Fin n)))
      - (c + ∫ t in ((R / 2 + R) / 2)..R,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
          (w : EuclideanSpace ℝ (Fin n))) = 0 := by
    haveI hnebot : (𝓝[Ioo (R / 2) R] R).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hab)]
      exact right_mem_Icc.2 hab.le
    have h1 := (hfcont R (right_mem_Icc.2 hab.le)).mono_left
      (nhdsWithin_mono R Ioo_subset_Icc_self)
    have h2 : Tendsto (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin n)))
        - (c + ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin n))))
            (w : EuclideanSpace ℝ (Fin n)))) (𝓝[Ioo (R / 2) R] R) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr using (hkey r hr).symm
    exact tendsto_nhds_unique h1 h2
  rw [htr]
  linarith [hfR]

end SphereTrace

/-! ## 2. The closure of the hemispherical cap body -/

/-- The recentred square norm of the folded point `capPt x` is `‖x‖²`. -/
theorem capPt_sq_th (x : EuclideanSpace ℝ (Fin (m + 1))) :
    ((capPt m x).1 + 1) ^ 2 + ‖(capPt m x).2‖ ^ 2 = ‖x‖ ^ 2 := by
  have h : ‖x‖ ^ 2 = (x 0) ^ 2 + ‖(ofEuclid m x).2‖ ^ 2 := by
    conv_lhs => rw [← toEuclid_ofEuclid (m := m) x]
    rw [norm_toEuclid_sq, ofEuclid_fst]
  have h1 : (capPt m x).1 + 1 = |x 0| := by
    show |x 0| - 1 + 1 = |x 0|
    ring
  have h2 : (capPt m x).2 = (ofEuclid m x).2 := rfl
  rw [h, h1, h2, sq_abs]

/-- **The closed half ball is contained in the closure of the hemispherical cap body.** -/
theorem mem_closure_body_th {p : CapSpace m} (h1 : -1 ≤ p.1)
    (h2 : (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 ≤ 1) :
    p ∈ closure ((hemisphere m).body) := by
  have ha : (0 : ℝ) ≤ p.1 + 1 := by linarith
  have hb : (0 : ℝ) ≤ ‖p.2‖ := norm_nonneg _
  set f : ℝ → CapSpace m := fun t => ((1 - t) / 2 + t * (p.1 + 1) - 1, t • p.2) with hfdef
  have hcont : Continuous f := by
    refine Continuous.prodMk (by fun_prop) ?_
    exact continuous_id.smul continuous_const
  have hf1 : f 1 = p := by
    refine Prod.ext ?_ ?_
    · show (1 - 1) / 2 + 1 * (p.1 + 1) - 1 = p.1
      ring
    · show (1 : ℝ) • p.2 = p.2
      rw [one_smul]
  have htend : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 p) := by
    rw [← hf1]
    exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  have h0 : ∀ᶠ t in 𝓝[<] (1 : ℝ), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h0, self_mem_nhdsWithin] with t ht0 ht1
  have ht1' : t < 1 := ht1
  have hnorm : ‖t • p.2‖ = t * ‖p.2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  rw [mem_hemisphere_body_iff]
  constructor
  · show -1 < (1 - t) / 2 + t * (p.1 + 1) - 1
    nlinarith
  · show ((1 - t) / 2 + t * (p.1 + 1) - 1 + 1) ^ 2 + ‖t • p.2‖ ^ 2 < 1
    rw [hnorm]
    set a := p.1 + 1 with hadef
    set b := ‖p.2‖ with hbdef
    have ha1 : a ≤ 1 := by nlinarith
    have hsq : t ^ 2 * a ^ 2 + t ^ 2 * b ^ 2 ≤ t ^ 2 := by nlinarith
    have e1 : (1 - t) * t * a ≤ (1 - t) * t := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) ht0.le)
        (by linarith : (0:ℝ) ≤ 1 - a)]
    have e2 : (1 - t) ^ 2 / 4 < 1 - t := by nlinarith
    nlinarith [hsq, e1, e2]

/-- The folded point of a point of the closed unit ball lies in the closure of the cap body. -/
theorem capPt_mem_closure_body_th {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : ‖x‖ ≤ 1) :
    capPt m x ∈ closure ((hemisphere m).body) := by
  refine mem_closure_body_th ?_ ?_
  · show -1 ≤ |x 0| - 1
    linarith [abs_nonneg (x 0)]
  · rw [capPt_sq_th]
    nlinarith [norm_nonneg x]

/-! ## 3. Measurability and integrability of the `Γ`-trace -/

/-- **The `Γ`-trace is measurable on the sphere.**  This discharges the measurability caveat
left open in `RobinCaps/ThinDomain/Reflect.lean`. -/
theorem aestronglyMeasurable_gammaTrace_th (u : H1P ((hemisphere m).body)) :
    AEStronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      gammaTrace u (w : EuclideanSpace ℝ (Fin (m + 1)))) (sphereMeasure (m + 1)) :=
  aestronglyMeasurable_traceSphere_th (by omega) one_pos (reflectEven u)

/-- **The squared `Γ`-trace is integrable**, unconditionally. -/
theorem integrable_gammaTrace_sq_th (u : H1P ((hemisphere m).body)) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (gammaTrace u (w : EuclideanSpace ℝ (Fin (m + 1)))) ^ 2) (sphereMeasure (m + 1)) :=
  integrable_traceSphere_sq_th (by omega) one_pos (reflectEven u)

/-- The `Γ`-trace is in `L²` of the sphere. -/
theorem memLp_gammaTrace_th (u : H1P ((hemisphere m).body)) :
    MemLp (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      gammaTrace u (w : EuclideanSpace ℝ (Fin (m + 1)))) 2 (sphereMeasure (m + 1)) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_gammaTrace_th u)).2
    (integrable_gammaTrace_sq_th u)

/-- The product of two `Γ`-traces is integrable (Cauchy–Schwarz). -/
theorem integrable_gammaTrace_mul_th (u v : H1P ((hemisphere m).body)) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      gammaTrace u (w : EuclideanSpace ℝ (Fin (m + 1)))
        * gammaTrace v (w : EuclideanSpace ℝ (Fin (m + 1)))) (sphereMeasure (m + 1)) :=
  (memLp_gammaTrace_th u).integrable_mul (memLp_gammaTrace_th v)

/-! ## 4. A pointwise-linear boundary representative -/

/-- Functions on the cap model vanishing `σ`-almost everywhere on the curved boundary `Γ`. -/
def nullGamma_th (m : ℕ) : Submodule ℝ (CapSpace m → ℝ) where
  carrier := {f | ∀ᵐ w ∂(sphereMeasure (m + 1)),
    f (ofBall m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1)))) = 0}
  zero_mem' := by
    show ∀ᵐ w ∂(sphereMeasure (m + 1)), (0 : CapSpace m → ℝ) (ofBall m
      ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))) = 0
    filter_upwards with w
    rfl
  add_mem' := by
    intro f g hf hg
    have hf' : ∀ᵐ w ∂(sphereMeasure (m + 1)), f (ofBall m
      ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))) = 0 := hf
    have hg' : ∀ᵐ w ∂(sphereMeasure (m + 1)), g (ofBall m
      ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))) = 0 := hg
    filter_upwards [hf', hg'] with w h1 h2
    show f _ + g _ = 0
    rw [h1, h2, add_zero]
  smul_mem' := by
    intro c f hf
    have hf' : ∀ᵐ w ∂(sphereMeasure (m + 1)), f (ofBall m
      ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))) = 0 := hf
    filter_upwards [hf'] with w h1
    show c * f _ = 0
    rw [h1, mul_zero]

theorem nullGamma_ae_th {f : CapSpace m → ℝ} (h : f ∈ nullGamma_th m) :
    ∀ᵐ w ∂(sphereMeasure (m + 1)),
      f (ofBall m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))) = 0 := h

theorem gammaTraceFun_ofBall_th (u : H1P ((hemisphere m).body))
    (x : EuclideanSpace ℝ (Fin (m + 1))) : gammaTraceFun u (ofBall m x) = gammaTrace u x := by
  rw [gammaTraceFun, toBall_ofBall]

/-- The class of the `Γ`-trace in the quotient by `nullGamma_th`: here linearity holds. -/
def gammaQ_th (m : ℕ) :
    H1P ((hemisphere m).body) →ₗ[ℝ] ((CapSpace m → ℝ) ⧸ nullGamma_th m) where
  toFun u := Submodule.Quotient.mk (gammaTraceFun u)
  map_add' u v := by
    have hmem : gammaTraceFun (u + v) - (gammaTraceFun u + gammaTraceFun v)
        ∈ nullGamma_th m := by
      filter_upwards [gammaTrace_add u v] with w hw
      show gammaTraceFun (u + v) (ofBall m _)
        - (gammaTraceFun u (ofBall m _) + gammaTraceFun v (ofBall m _)) = 0
      rw [gammaTraceFun_ofBall_th, gammaTraceFun_ofBall_th, gammaTraceFun_ofBall_th, hw]
      ring
    have h := (Submodule.Quotient.eq (nullGamma_th m)).2 hmem
    rw [h]
    rfl
  map_smul' c u := by
    have hfun : gammaTraceFun (c • u) = c • gammaTraceFun u := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      exact gammaTrace_smul c u _
    simp only [hfun, RingHom.id_apply]
    rfl

theorem exists_gammaSection_th (m : ℕ) :
    ∃ s : ((CapSpace m → ℝ) ⧸ nullGamma_th m) →ₗ[ℝ] (CapSpace m → ℝ),
      (nullGamma_th m).mkQ.comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)

/-- **A linear section** of the quotient map by `nullGamma_th m`. -/
def gammaSection_th (m : ℕ) :
    ((CapSpace m → ℝ) ⧸ nullGamma_th m) →ₗ[ℝ] (CapSpace m → ℝ) :=
  Classical.choose (exists_gammaSection_th m)

theorem gammaSection_spec_th (m : ℕ) (q : (CapSpace m → ℝ) ⧸ nullGamma_th m) :
    (Submodule.Quotient.mk (gammaSection_th m q) : (CapSpace m → ℝ) ⧸ nullGamma_th m) = q := by
  have h := congrArg
    (fun F : ((CapSpace m → ℝ) ⧸ nullGamma_th m) →ₗ[ℝ] ((CapSpace m → ℝ) ⧸ nullGamma_th m) => F q)
    (Classical.choose_spec (exists_gammaSection_th m))
  simpa only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    LinearMap.id_coe, id_eq] using h

theorem gammaSection_sub_mem_th (m : ℕ) (f : CapSpace m → ℝ) :
    gammaSection_th m (Submodule.Quotient.mk f) - f ∈ nullGamma_th m :=
  (Submodule.Quotient.eq (nullGamma_th m)).1 (gammaSection_spec_th m _)

/-- **The pointwise-linear `Γ`-trace**: a genuinely linear boundary representative which
agrees `σ`-almost everywhere with `gammaTrace`. -/
def trGamma_th (m : ℕ) : H1P ((hemisphere m).body) →ₗ[ℝ] (CapSpace m → ℝ) :=
  (gammaSection_th m).comp (gammaQ_th m)

theorem trGamma_ae_th (u : H1P ((hemisphere m).body)) :
    ∀ᵐ w ∂(sphereMeasure (m + 1)),
      trGamma_th m u (ofBall m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))
        = gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) := by
  have h := nullGamma_ae_th (gammaSection_sub_mem_th m (gammaTraceFun u))
  filter_upwards [h] with w hw
  have hw' : gammaSection_th m (Submodule.Quotient.mk (gammaTraceFun u)) (ofBall m _)
      - gammaTraceFun u (ofBall m _) = 0 := hw
  rw [gammaTraceFun_ofBall_th] at hw'
  have : trGamma_th m u (ofBall m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))))
      = gammaSection_th m (Submodule.Quotient.mk (gammaTraceFun u)) (ofBall m
        ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))) := rfl
  rw [this]
  linarith

/-! ## 5. The boundary form -/

/-- The direction set of the curved boundary `Γ`: the open upper half sphere. -/
def upperSphere_th (m : ℕ) : Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
  {w | 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0}

theorem measurableSet_upperSphere_th : MeasurableSet (upperSphere_th m) :=
  measurableSet_upperSphere_rf

/-- **The `Γ`-form of the hemispherical cap**, as an integral over the upper half sphere. -/
def gammaForm_th (u v : H1P ((hemisphere m).body)) : ℝ :=
  ∫ w in upperSphere_th m,
    gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1)))
      * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1))) ∂(sphereMeasure (m + 1))

theorem gammaForm_symm_th (u v : H1P ((hemisphere m).body)) :
    gammaForm_th u v = gammaForm_th v u :=
  setIntegral_congr_fun measurableSet_upperSphere_th fun _ _ => mul_comm _ _

theorem gammaForm_add_left_th (u u' v : H1P ((hemisphere m).body)) :
    gammaForm_th (u + u') v = gammaForm_th u v + gammaForm_th u' v := by
  have hae : ∀ᵐ w ∂((sphereMeasure (m + 1)).restrict (upperSphere_th m)),
      gammaTrace (u + u') ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
      = gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
        + gammaTrace u' ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
    filter_upwards [ae_restrict_of_ae (gammaTrace_add u u')] with w hw
    rw [hw]
    ring
  rw [gammaForm_th, integral_congr_ae hae,
    integral_add (integrable_gammaTrace_mul_th u v).integrableOn
      (integrable_gammaTrace_mul_th u' v).integrableOn]
  rfl

theorem gammaForm_smul_left_th (c : ℝ) (u v : H1P ((hemisphere m).body)) :
    gammaForm_th (c • u) v = c • gammaForm_th u v := by
  rw [smul_eq_mul, gammaForm_th, gammaForm_th, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_upperSphere_th fun w _ => ?_
  rw [gammaTrace_smul]
  ring

theorem gammaForm_add_right_th (u v v' : H1P ((hemisphere m).body)) :
    gammaForm_th u (v + v') = gammaForm_th u v + gammaForm_th u v' := by
  rw [gammaForm_symm_th, gammaForm_add_left_th, gammaForm_symm_th v u, gammaForm_symm_th v' u]

theorem gammaForm_smul_right_th (c : ℝ) (u v : H1P ((hemisphere m).body)) :
    gammaForm_th u (c • v) = c • gammaForm_th u v := by
  rw [gammaForm_symm_th, gammaForm_smul_left_th, gammaForm_symm_th v u]

theorem gammaForm_nonneg_th (u : H1P ((hemisphere m).body)) : 0 ≤ gammaForm_th u u :=
  setIntegral_nonneg measurableSet_upperSphere_th fun _ _ => mul_self_nonneg _

/-- The `Γ`-form, bundled as a bilinear map. -/
def bdGamma_th (m : ℕ) :
    H1P ((hemisphere m).body) →ₗ[ℝ] H1P ((hemisphere m).body) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ gammaForm_th gammaForm_add_left_th gammaForm_smul_left_th
    gammaForm_add_right_th gammaForm_smul_right_th

@[simp] theorem bdGamma_apply_th (u v : H1P ((hemisphere m).body)) :
    bdGamma_th m u v = gammaForm_th u v := rfl

/-! ## 6. The bridge to the revolution boundary integral -/

/-- The terminal disk of the unit hemispherical end cap is degenerate. -/
theorem hemisphere_theta_zero_th (m : ℕ) : (hemisphere m).θ 0 = 0 := by
  show Real.sqrt (1 - (0 + 1) ^ 2) = 0
  norm_num

/-- The cap's boundary integrand of a product is the indicator of the upper half sphere. -/
theorem capSphereFun_mul_th (f g : CapSpace m → ℝ)
    (w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    capSphereFun m (fun p => f p * g p) w
      = Set.indicator (upperSphere_th m)
          (fun w => f (ofBall m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1))))
            * g (ofBall m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1))))) w := by
  by_cases hw : w ∈ upperSphere_th m
  · have hw' : 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 := hw
    rw [Set.indicator_of_mem hw]
    show (if 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 then _ else (0 : ℝ)) = _
    rw [if_pos hw']
    rfl
  · have hw' : ¬ (0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0) := hw
    rw [Set.indicator_of_notMem hw]
    show (if 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 then _ else (0 : ℝ)) = 0
    rw [if_neg hw']

/-- The lateral boundary integral of the product of the two pointwise-linear traces is the
sphere integral of the product of the two `Γ`-traces. -/
theorem capLateralIntegral_trGamma_th (hm : 1 ≤ m) (u v : H1P ((hemisphere m).body)) :
    capLateralIntegral (hemisphere m) (fun p => trGamma_th m u p * trGamma_th m v p)
      = gammaForm_th u v := by
  have hae : (capSphereFun m (fun p => trGamma_th m u p * trGamma_th m v p))
      =ᵐ[sphereMeasure (m + 1)]
      Set.indicator (upperSphere_th m)
        (fun w => gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))) := by
    filter_upwards [trGamma_ae_th u, trGamma_ae_th v] with w h1 h2
    rw [capSphereFun_mul_th]
    by_cases hw : w ∈ upperSphere_th m
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, h1, h2]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
  have hint : Integrable (capSphereFun m (fun p => trGamma_th m u p * trGamma_th m v p))
      (sphereMeasure (m + 1)) :=
    ((integrable_gammaTrace_mul_th u v).indicator measurableSet_upperSphere_th).congr hae.symm
  rw [capLateralIntegral_hemisphere_eq m hm _ hint, integral_congr_ae hae,
    integral_indicator measurableSet_upperSphere_th]
  rfl

/-- **The `Γ`-pairing of `RobinCaps/Cap/LowerWeak.lean` is the sphere form.** -/
theorem capGammaPair_trGamma_th (hm : 1 ≤ m) (u v : H1P ((hemisphere m).body)) :
    capGammaPair (hemisphere m) (trGamma_th m u) (trGamma_th m v) = gammaForm_th u v := by
  rw [capGammaPair, hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty,
    integral_zero_measure, add_zero, capLateralIntegral_trGamma_th hm]

/-! ## 7. Consistency on functions continuous up to the boundary -/

/-- For a representative continuous on the closed cap the `Γ`-trace is the boundary
restriction. -/
theorem gammaTrace_eq_of_continuousOn_th (u : H1P ((hemisphere m).body))
    (hcont : ContinuousOn u.toFun (closure ((hemisphere m).body))) :
    ∀ᵐ w ∂(sphereMeasure (m + 1)),
      gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        = u.toFun (capPt m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))) := by
  have hslice : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      ContinuousOn (fun r : ℝ => (reflectEven u).toFun
        (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))) (Icc ((1 : ℝ) / 2) 1) := by
    intro w
    have hmaps : MapsTo (fun r : ℝ => capPt m
        (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))))) (Icc ((1 : ℝ) / 2) 1)
        (closure ((hemisphere m).body)) := by
      intro r hr
      refine capPt_mem_closure_body_th ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hr.1] : (0 : ℝ) ≤ r),
        mem_sphere_zero_iff_norm.1 w.2, mul_one]
      exact hr.2
    have hc : Continuous fun r : ℝ => capPt m
        (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))) :=
      continuous_capPt.comp (continuous_id.smul continuous_const)
    exact hcont.comp hc.continuousOn hmaps
  have h := traceSphere_eq_of_continuousOn_th (n := m + 1) (by omega) one_pos
    (reflectEven u) hslice
  filter_upwards [h] with w hw
  rw [gammaTrace_eq, hw, one_smul]
  rfl

/-- **The `Γ`-form is the exposed boundary energy on continuous representatives.** -/
theorem gammaForm_self_eq_capBoundary_th (hm : 1 ≤ m) (u : H1P ((hemisphere m).body))
    (hcont : ContinuousOn u.toFun (closure ((hemisphere m).body))) :
    gammaForm_th u u = capBoundary (hemisphere m) u.toFun := by
  have hae := gammaTrace_eq_of_continuousOn_th u hcont
  have hsq : (fun p : CapSpace m => u.toFun p ^ 2) = fun p => u.toFun p * u.toFun p := by
    funext p
    rw [sq]
  have haeI : (capSphereFun m (fun p => u.toFun p ^ 2)) =ᵐ[sphereMeasure (m + 1)]
      Set.indicator (upperSphere_th m)
        (fun w => gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          * gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))) := by
    rw [hsq]
    filter_upwards [hae] with w hw
    rw [capSphereFun_mul_th]
    by_cases hwm : w ∈ upperSphere_th m
    · have hwm' : (0 : ℝ) < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 := hwm
      rw [Set.indicator_of_mem hwm, Set.indicator_of_mem hwm, hw,
        capPt_eq_ofBall (le_of_lt hwm')]
    · rw [Set.indicator_of_notMem hwm, Set.indicator_of_notMem hwm]
  have hint : Integrable (capSphereFun m (fun p => u.toFun p ^ 2)) (sphereMeasure (m + 1)) :=
    ((integrable_gammaTrace_mul_th u u).indicator measurableSet_upperSphere_th).congr haeI.symm
  rw [capBoundary, hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty,
    integral_zero_measure, add_zero, capLateralIntegral_hemisphere_eq m hm _ hint,
    integral_congr_ae haeI, integral_indicator measurableSet_upperSphere_th]
  rfl

/-! ## 8. The trace of an a.e.-vanishing element -/

/-- A function vanishing a.e. on the cap body pulls back to a function vanishing a.e. on the
whole unit ball under the folding map. -/
theorem capPt_comp_ae_zero_th {β : Type*} [NormedAddCommGroup β] {f : CapSpace m → β}
    (hf : f =ᵐ[volume.restrict ((hemisphere m).body)] 0) :
    (fun x => f (capPt m x))
      =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)] 0 := by
  rw [restrict_ball_eq_rf]
  refine Filter.Eventually.filter_mono (ae_mono (Measure.restrict_union_le _ _)) ?_
  refine ae_add_measure_iff.2 ⟨?_, ?_⟩
  · have h1 := (measurePreserving_ofBall_upper m).quasiMeasurePreserving.ae_eq_comp hf
    filter_upwards [h1, ae_restrict_mem measurableSet_upperHalfBall] with x hx hmem
    show f (capPt m x) = 0
    rw [capPt_eq_ofBall (le_of_lt hmem.2)]
    exact hx
  · have h1 := (measurePreserving_ofBallNeg_lower m).quasiMeasurePreserving.ae_eq_comp hf
    filter_upwards [h1, ae_restrict_mem measurableSet_lowerHalfBall] with x hx hmem
    show f (capPt m x) = 0
    rw [capPt_eq_ofBallNeg (le_of_lt hmem.2)]
    exact hx

/-- **The `Γ`-trace of an a.e.-vanishing element vanishes almost everywhere.** -/
theorem gammaTrace_ae_zero_th (u : H1P ((hemisphere m).body))
    (hu : u.toFun =ᵐ[volume.restrict ((hemisphere m).body)] 0) :
    ∀ᵐ w ∂(sphereMeasure (m + 1)),
      gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
        EuclideanSpace ℝ (Fin (m + 1))) = 0 := by
  have hnull : u ∈ nullAEP ((hemisphere m).body) := hu
  have hgx := gx_ae_zero_of_mem_nullAEP isOpen_body_rf hnull
  have hgz := gz_ae_zero_of_mem_nullAEP isOpen_body_rf hnull
  have hv : reflectEvenFun u.toFun
      =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)] 0 :=
    capPt_comp_ae_zero_th hu
  have hgxb := capPt_comp_ae_zero_th hgx
  have hgzb := capPt_comp_ae_zero_th hgz
  have hg : reflectEvenGrad u.gx u.gz
      =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)] 0 := by
    filter_upwards [hgxb, hgzb] with x h1 h2
    have h1' : u.gx (capPt m x) = 0 := h1
    have h2' : u.gz (capPt m x) = 0 := h2
    show toEuclid m (sgn0 x * u.gx (capPt m x), u.gz (capPt m x)) = 0
    rw [h1', h2', mul_zero]
    exact (capLinearEquiv m).map_zero
  filter_upwards [ae_radial_congr_th (n := m + 1) (R := 1) (by omega) hv,
    ae_radial_congr_th (n := m + 1) (R := 1) (by omega) hg] with w hw1 hw2
  have hcg := traceSphere_congr_th (n := m + 1) (R := 1) one_pos hw1 hw2
  show traceSphere 1 (reflectEvenFun u.toFun) (reflectEvenGrad u.gx u.gz) _ = 0
  rw [hcg]
  simp [traceSphere]

theorem gammaForm_eq_zero_of_ae_zero_th (u : H1P ((hemisphere m).body))
    (hu : u.toFun =ᵐ[volume.restrict ((hemisphere m).body)] 0)
    (v : H1P ((hemisphere m).body)) : gammaForm_th u v = 0 := by
  have h := gammaTrace_ae_zero_th u hu
  have hzero : ∀ᵐ w ∂((sphereMeasure (m + 1)).restrict (upperSphere_th m)),
      gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) = 0 := by
    filter_upwards [ae_restrict_of_ae h] with w hw
    rw [hw, zero_mul]
  rw [gammaForm_th, integral_congr_ae hzero, integral_zero]

/-! ## 9. The trace inequality -/

theorem gammaForm_self_le_th (u : H1P ((hemisphere m).body)) :
    gammaForm_th u u ≤ 2 * max (4 * 2 ^ m) (2 ^ m) * (massP u + dirichletP u) := by
  refine le_trans ?_ (gammaTrace_sq_integral_le u)
  have hcongr : gammaForm_th u u
      = ∫ w in upperSphere_th m,
        (gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))) ^ 2 ∂(sphereMeasure (m + 1)) :=
    setIntegral_congr_fun measurableSet_upperSphere_th fun _ _ => (sq _).symm
  rw [hcongr]
  exact setIntegral_le_integral (integrable_gammaTrace_sq_th u)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-! ## 10. The `CapTraceData` instance -/

/-- **The `CapTraceData` of the unit hemispherical end cap**, built from the reflection trace of
`RobinCaps/ThinDomain/Reflect.lean`. -/
def capTraceDataHemi_th (m : ℕ) (hm : 1 ≤ m) : CapTraceData (hemisphere m) where
  trΓ u := trGamma_th m u
  trΓ_add u v := (trGamma_th m).map_add u v
  trΓ_smul c u := (trGamma_th m).map_smul c u
  bdΓ := bdGamma_th m
  bdΓ_eq u v := (capGammaPair_trGamma_th hm u v).symm
  bdΓ_symm u v := gammaForm_symm_th u v
  bdΓ_nonneg u := gammaForm_nonneg_th u
  trΓ_continuous u hu := gammaForm_self_eq_capBoundary_th hm u hu
  traceConst := 2 * max (4 * 2 ^ m) (2 ^ m)
  traceConst_nonneg := by positivity
  trace_ineq u := by
    have h := gammaForm_self_le_th u
    rw [add_comm (dirichletP u) (massP u)]
    exact h
  vanishes_ae u hu v := gammaForm_eq_zero_of_ae_zero_th u hu v

/-- **The boundary form of the instance in its sphere-integral form.** -/
theorem capTraceDataHemi_bdΓ_eq_th (m : ℕ) (hm : 1 ≤ m) (u : H1P ((hemisphere m).body)) :
    (capTraceDataHemi_th m hm).bdΓ u u
      = ∫ w in {w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0},
        (gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))) ^ 2 ∂(sphereMeasure (m + 1)) :=
  setIntegral_congr_fun measurableSet_upperSphere_th fun _ _ => (sq _).symm

end

end RobinCaps.Cap

