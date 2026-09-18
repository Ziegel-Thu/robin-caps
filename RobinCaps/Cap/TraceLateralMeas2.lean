import RobinCaps.Cap.TraceLateralMeas

/-!
# The `θ`-parametrised lateral trace is jointly almost-everywhere strongly measurable

This file finishes what `RobinCaps/Cap/TraceLateralMeas.lean` left open: an **unconditional**
proof of the two hypotheses `hJoint`/`hJointAE` of
`RobinCaps.Cap.aestronglyMeasurable_lateralTraceGen_tlg`, hence of the headline statement
`aestronglyMeasurable_lateralTraceGen_tl2` below, with **no** hypothesis on `C.θ` beyond what the
`Cap` structure already supplies.

## Strategy

Never ask for measurability of `C.θ` itself (it is unconstrained off `Set.Ioo (-C.K) 0`, see the
docstring of `TraceLateralMeas.lean`).  Work throughout with the globally measurable, globally
positive extension `thetaExt_tlm C` of `TraceLateralMeas.lean`, which agrees with `C.θ` *exactly*
on `Set.Ioo (-C.K) 0`.

1. `stronglyMeasurable_traceSphere_thetaExt_tl2`: joint strong measurability of the
   `thetaExt_tlm C`-parametrised sphere trace of the canonical measurable representatives
   `repFun`, `repGz_el`, by feeding `thetaExt_tlm C` (unconditionally measurable and positive,
   `measurable_thetaExt_tlm`/`thetaExt_pos_tlm`) into `stronglyMeasurable_traceSphere_paramR_tlm`.
2. `ae_radial_congr_body_tl2`: the variable-radius analogue of
   `RobinCaps.ThinDomain.ae_radial_congr_joint_tgb` (there for a fixed-radius bulk cylinder) and of
   `RobinCaps.Cap.ae_radial_congr_th` (there for a single fixed-radius ball): an a.e. equality on
   `C.body` transports to a joint a.e. statement along rays, with the radial cutoff
   `thetaExt_tlm C p.1` in place of a constant `R`.  The measurable-null-superset technique is
   identical, with the joint measurability of the "radial indicator mass"
   `Θ p = ∫ r in Ioo 0 (thetaExt_tlm C p.1), r ^ (m-1) * 1_N (p.1, r • p.2)` supplied by
   `stronglyMeasurable_Theta_tlm` (`TraceLateralMeas.lean` §5) and the Fubini/polar identity
   supplied by `integral_body_eq_integral_axial_slices_tlg` (axial-outer Fubini on `C.body`,
   `TraceLateralGen.lean` §4) composed, level by level, with `integral_ball_polar_symm`.
3. `ae_traceSphere_congr_tl2`: applying step 2 to the a.e. equalities
   `repFun C u =ᵐ[C.body] u.toFun` and `repGz_el C u =ᵐ[C.body] u.gz`, then `traceSphere_congr_th`
   slice-wise (using `thetaExt_eq_tlm` to identify `thetaExt_tlm C p.1` with `C.θ p.1` for a.e.
   `p.1 ∈ Ioo (-C.K) 0`), gives the joint a.e. identification of the `thetaExt_tlm C`-trace of the
   representatives with the honest `C.θ`-trace of `u`.
4. `aestronglyMeasurable_lateralTraceGen_tl2`: combine steps 1 and 3 with the defining identity
   `lateralTraceGen_apply_tlg` to exhibit `lateralTraceGen_tlg C u (·, C.θ · • ·)` as a.e. equal to
   the strongly measurable function of step 1.  `lateralMeas_tl2` packages this as a one-line
   corollary quantified over `u`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace RobinCaps.Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 1. Joint measurability of the `thetaExt_tlm`-parametrised trace, unconditionally -/

/-- **Joint strong measurability of the `thetaExt_tlm C`-parametrised sphere trace of the
canonical measurable representatives.**  Unlike `stronglyMeasurable_traceSphere_theta_joint_tlm`
of `TraceLateralMeas.lean`, this is unconditional: `thetaExt_tlm C` is globally measurable and
globally positive by construction. -/
theorem stronglyMeasurable_traceSphere_thetaExt_tl2 (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable
      (fun p : ℝ × sphere (0 : E) 1 =>
        traceSphere (thetaExt_tlm C p.1) (fun z => repFun C u (p.1, z))
          (fun z => repGz_el C u (p.1, z)) ((p.2 : E))) :=
  stronglyMeasurable_traceSphere_paramR_tlm (measurable_thetaExt_tlm C) (thetaExt_pos_tlm C)
    (stronglyMeasurable_repFun C u) (stronglyMeasurable_repGz_el C u)

/-! ## 2. Transporting an a.e. equality on `C.body` to a joint a.e. statement along rays -/

/-- **The variable-radius transport lemma.**  An a.e. equality on `C.body` passes to a joint
a.e. statement along rays, with the radial cutoff `thetaExt_tlm C p.1`.  This is the
variable-radius analogue of `RobinCaps.ThinDomain.ae_radial_congr_joint_tgb`. -/
theorem ae_radial_congr_body_tl2 (hm : 1 ≤ m) (C : Cap m) {α : Type*}
    {f₁ f₂ : CapSpace m → α} (h : f₁ =ᵐ[volume.restrict C.body] f₂) :
    ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m)),
      ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) (thetaExt_tlm C p.1))),
        f₁ (p.1, r • (p.2 : E)) = f₂ (p.1, r • (p.2 : E)) := by
  classical
  haveI : IsFiniteMeasure (sphereMeasure m) := isFiniteMeasure_sphereMeasure_tlm
  haveI hIooFin : IsFiniteMeasure (volume.restrict (Ioo (-C.K) (0 : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hne : volume.restrict C.body {p | ¬ f₁ p = f₂ p} = 0 := ae_iff.1 h
  obtain ⟨N, hNsup, hNmeas, hN0⟩ := exists_measurable_superset_of_null hne
  set indN : CapSpace m → ℝ := N.indicator (fun _ => (1 : ℝ)) with hindN_def
  have hindNmeas : Measurable indN := measurable_const.indicator hNmeas
  have hindNnn : ∀ p, 0 ≤ indN p := fun p => by
    by_cases hp : p ∈ N
    · rw [hindN_def]; simp [Set.indicator_of_mem hp]
    · rw [hindN_def]; simp [Set.indicator_of_notMem hp]
  have hindNle : ∀ p, indN p ≤ 1 := fun p => by
    by_cases hp : p ∈ N
    · rw [hindN_def]; simp [Set.indicator_of_mem hp]
    · rw [hindN_def]; simp [Set.indicator_of_notMem hp]
  have hindNint : Integrable indN (volume.restrict C.body) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hindNmeas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hindNnn p)]
    exact hindNle p
  have hindNbodyInt : Integrable (C.body.indicator indN) volume :=
    (integrable_indicator_iff (measurableSet_body' C)).2 hindNint
  have hindNzero : (∫ p in C.body, indN p) = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hmemN : ∀ᵐ p ∂(volume.restrict C.body), p ∉ N := by
      rw [ae_iff]; simpa using hN0
    filter_upwards [hmemN] with p hp
    rw [hindN_def]
    exact Set.indicator_of_notMem hp _
  -- The joint radial indicator mass `Θ`, whose strong measurability is `stronglyMeasurable_Theta_tlm`.
  set Θ : ℝ × sphere (0 : E) 1 → ℝ :=
    fun p => ∫ r in Ioo (0 : ℝ) (thetaExt_tlm C p.1), r ^ (m - 1) * indN (p.1, r • (p.2 : E))
      with hΘ_def
  have hΘmeas : StronglyMeasurable Θ := stronglyMeasurable_Theta_tlm C hNmeas
  have hΘnn : ∀ p, 0 ≤ Θ p := by
    intro p
    refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
    exact mul_nonneg (pow_nonneg hr.1.le _) (hindNnn _)
  -- Bound `Θ` by the fixed constant `∫ r in Ioo 0 1, r ^ (m - 1)`, using `thetaExt_le_one_tlm`.
  have hpowint1 : IntegrableOn (fun r : ℝ => r ^ (m - 1)) (Ioo (0 : ℝ) 1) :=
    ((continuous_pow (m - 1)).integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
      Ioo_subset_Icc_self
  have hHmeasP : ∀ p : ℝ × sphere (0 : E) 1,
      Measurable (fun r : ℝ => indN (p.1, r • (p.2 : E))) := fun p =>
    hindNmeas.comp (measurable_const.prodMk (measurable_id.smul measurable_const))
  have hHrint1 : ∀ p : ℝ × sphere (0 : E) 1,
      IntegrableOn (fun r => r ^ (m - 1) * indN (p.1, r • (p.2 : E))) (Ioo (0 : ℝ) 1) := by
    intro p
    refine Integrable.mono' hpowint1
      (((measurable_id.pow_const (m - 1)).mul (hHmeasP p)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hrp : (0 : ℝ) ≤ r ^ (m - 1) := pow_nonneg hr.1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrp (hindNnn _))]
    calc r ^ (m - 1) * indN (p.1, r • (p.2 : E)) ≤ r ^ (m - 1) * 1 :=
          mul_le_mul_of_nonneg_left (hindNle _) hrp
      _ = r ^ (m - 1) := mul_one _
  have hHrint : ∀ p : ℝ × sphere (0 : E) 1,
      IntegrableOn (fun r => r ^ (m - 1) * indN (p.1, r • (p.2 : E)))
        (Ioo (0 : ℝ) (thetaExt_tlm C p.1)) :=
    fun p => (hHrint1 p).mono_set (Ioo_subset_Ioo_right (thetaExt_le_one_tlm C p.1))
  have hΘle : ∀ p : ℝ × sphere (0 : E) 1, Θ p ≤ ∫ r in Ioo (0 : ℝ) 1, r ^ (m - 1) := by
    intro p
    have hsub : Ioo (0 : ℝ) (thetaExt_tlm C p.1) ≤ᵐ[volume] Ioo (0 : ℝ) (1 : ℝ) :=
      HasSubset.Subset.eventuallyLE (Ioo_subset_Ioo_right (thetaExt_le_one_tlm C p.1))
    have hnn1 : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) (1 : ℝ))]
        fun r => r ^ (m - 1) * indN (p.1, r • (p.2 : E)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact mul_nonneg (pow_nonneg hr.1.le _) (hindNnn _)
    calc Θ p = ∫ r in Ioo (0 : ℝ) (thetaExt_tlm C p.1), r ^ (m - 1) * indN (p.1, r • (p.2 : E)) :=
          rfl
      _ ≤ ∫ r in Ioo (0 : ℝ) (1 : ℝ), r ^ (m - 1) * indN (p.1, r • (p.2 : E)) :=
          setIntegral_mono_set (hHrint1 p) hnn1 hsub
      _ ≤ ∫ r in Ioo (0 : ℝ) (1 : ℝ), r ^ (m - 1) := by
          refine setIntegral_mono_on (hHrint1 p) hpowint1 measurableSet_Ioo (fun r hr => ?_)
          have hrp : (0 : ℝ) ≤ r ^ (m - 1) := pow_nonneg hr.1.le _
          calc r ^ (m - 1) * indN (p.1, r • (p.2 : E)) ≤ r ^ (m - 1) * 1 :=
                mul_le_mul_of_nonneg_left (hindNle _) hrp
            _ = r ^ (m - 1) := mul_one _
  have hΘint : Integrable Θ ((volume.restrict (Ioo (-C.K) (0 : ℝ))).prod (sphereMeasure m)) := by
    refine Integrable.mono' (integrable_const (∫ r in Ioo (0 : ℝ) 1, r ^ (m - 1)))
      hΘmeas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hΘnn p)]
    exact hΘle p
  have hFubini : (∫ p, Θ p ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m)))
      = ∫ s in Ioo (-C.K) 0, ∫ w, Θ (s, w) ∂(sphereMeasure m) := integral_prod Θ hΘint
  -- For a.e. axial level `s`, the transverse slice of `indN` is integrable on the ball of
  -- radius `θ s`.
  have hBodyProd : Integrable (fun p => (C.body.indicator indN) p) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hindNbodyInt
  have hae_int : ∀ᵐ s ∂(volume : Measure ℝ),
      Integrable (fun z => (C.body.indicator indN) (s, z)) volume := hBodyProd.prod_right_ae
  have hae_int' : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (0 : ℝ))),
      IntegrableOn (fun z => indN (s, z)) (ball (0 : E) (C.θ s)) volume := by
    filter_upwards [ae_restrict_of_ae hae_int, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    have heq : (fun z => (C.body.indicator indN) (s, z))
        = (ball (0 : E) (C.θ s)).indicator (fun z => indN (s, z)) :=
      funext fun z => indicator_body_transverse_el C indN hsmem z
    rw [heq] at hs
    exact (integrable_indicator_iff measurableSet_ball).1 hs
  have hae_polar : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (0 : ℝ))),
      (∫ w, Θ (s, w) ∂(sphereMeasure m)) = ∫ z in ball (0 : E) (C.θ s), indN (s, z) := by
    filter_upwards [hae_int', ae_restrict_mem measurableSet_Ioo] with s hballInt hsmem
    have hextEq : thetaExt_tlm C s = C.θ s := thetaExt_eq_tlm C hsmem
    have hΘeqpt : ∀ w : sphere (0 : E) 1,
        Θ (s, w) = ∫ r in Ioo (0 : ℝ) (C.θ s), r ^ (m - 1) * indN (s, r • (w : E)) := by
      intro w
      simp only [hΘ_def, hextEq]
    rw [integral_congr_ae (Eventually.of_forall hΘeqpt)]
    exact (integral_ball_polar_symm hm hballInt).symm
  have hprodzero : (∫ p, Θ p ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m))) = 0 := by
    rw [hFubini, integral_congr_ae hae_polar,
      ← integral_body_eq_integral_axial_slices_tlg C hindNbodyInt]
    exact hindNzero
  have hΘzero : ∀ᵐ p ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m)), Θ p = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hΘnn) hΘint).1 hprodzero
  filter_upwards [hΘzero] with p hp
  have hHnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) (thetaExt_tlm C p.1))]
      fun r => r ^ (m - 1) * indN (p.1, r • (p.2 : E)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_nonneg (pow_nonneg hr.1.le _) (hindNnn _)
  have hrzero : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) (thetaExt_tlm C p.1))),
      r ^ (m - 1) * indN (p.1, r • (p.2 : E)) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hHnn (hHrint p)).1 hp
  filter_upwards [hrzero, ae_restrict_mem measurableSet_Ioo] with r hr0 hrmem
  have hrp : (0 : ℝ) < r ^ (m - 1) := pow_pos hrmem.1 _
  have hind0 : indN (p.1, r • (p.2 : E)) = 0 := by
    rcases mul_eq_zero.1 hr0 with h' | h'
    · exact absurd h' hrp.ne'
    · exact h'
  have hnotN : (p.1, r • (p.2 : E)) ∉ N := by
    intro hmemN
    rw [hindN_def, Set.indicator_of_mem hmemN] at hind0
    exact one_ne_zero hind0
  by_contra hcon
  exact hnotN (hNsup hcon)

/-! ## 3. Identifying the `thetaExt_tlm`-trace of the representatives with the `C.θ`-trace of `u` -/

/-- **The `thetaExt_tlm C`-trace of the canonical representatives agrees, jointly a.e., with the
honest `C.θ`-trace of `u` itself.** -/
theorem ae_traceSphere_congr_tl2 (hm : 1 ≤ m) (C : Cap m) (u : H1P C.body) :
    ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m)),
      traceSphere (thetaExt_tlm C p.1) (fun z => repFun C u (p.1, z))
          (fun z => repGz_el C u (p.1, z)) ((p.2 : E))
        = traceSphere (C.θ p.1) (fun z => u.toFun (p.1, z)) (fun z => u.gz (p.1, z))
            ((p.2 : E)) := by
  have hv := ae_radial_congr_body_tl2 (α := ℝ) hm C
    (f₁ := repFun C u) (f₂ := u.toFun) u.memL2.aestronglyMeasurable.ae_eq_mk.symm
  have hg := ae_radial_congr_body_tl2 (α := E) hm C
    (f₁ := repGz_el C u) (f₂ := u.gz) (repGz_ae_eq_el C u).symm
  have h0 : ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m)),
      p.1 ∈ Ioo (-C.K) (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hv, hg, h0] with p hvp hgp hp1
  have hθs : 0 < C.θ p.1 := C.θ_pos p.1 hp1
  have hext : thetaExt_tlm C p.1 = C.θ p.1 := thetaExt_eq_tlm C hp1
  rw [hext] at hvp hgp ⊢
  exact traceSphere_congr_th hθs hvp hgp

/-! ## 4. Deliverable: unconditional joint measurability of the lateral trace -/

/-- **Deliverable.**  The `θ`-parametrised lateral trace of `u ∈ H¹(𝒞)` on the surface of
revolution is jointly almost-everywhere strongly measurable, with no hypothesis on `C.θ` beyond
what the `Cap` structure itself supplies. -/
theorem aestronglyMeasurable_lateralTraceGen_tl2 (hm : 1 ≤ m) (C : Cap m)
    (u : H1P C.body) :
    AEStronglyMeasurable
      (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
      ((volume.restrict (Set.Ioo (-C.K) 0)).prod (sphereMeasure m)) := by
  refine ⟨fun p => traceSphere (thetaExt_tlm C p.1) (fun z => repFun C u (p.1, z))
      (fun z => repGz_el C u (p.1, z)) ((p.2 : E)),
    stronglyMeasurable_traceSphere_thetaExt_tl2 C u, ?_⟩
  have h0 : ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo (-C.K) 0)).prod (sphereMeasure m)),
      p.1 ∈ Ioo (-C.K) (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [ae_traceSphere_congr_tl2 hm C u, h0] with p hcongr hp1
  rw [lateralTraceGen_apply_tlg C u hp1 p.2, hcongr]

/-- **Packaged corollary**, quantified over `u`. -/
theorem lateralMeas_tl2 (hm : 1 ≤ m) (C : Cap m) (u : H1P C.body) :
    AEStronglyMeasurable
      (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
      ((volume.restrict (Set.Ioo (-C.K) 0)).prod (sphereMeasure m)) :=
  aestronglyMeasurable_lateralTraceGen_tl2 hm C u

end
end RobinCaps.Cap
