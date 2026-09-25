import RobinCaps.Compact.ConvexRellichIface

/-!
# (A1) on a general bounded convex domain (wave 12)

This file proves `approxEstimateCvx_acx`: the convex-domain analogue of `(A1)`
(`RobinCaps/Compact/Approx.lean`, `integral_ball_approx_sub_sq_le'`), assuming the two smooth
estimates `SmoothConvSetEst`/`SmoothDilateSetEst` of `RobinCaps/Compact/ConvexRellichIface.lean`
(proved elsewhere, on `Compact/SmoothEstimatesSet.lean`).

## Route

For `Ω` bounded, convex, open, with `ball 0 r₀ ⊆ Ω ⊆ closedBall 0 ρ₀`, and `u ∈ H¹(Ω)`,
`1/2 ≤ lam < 1`, `0 < ε < (1-lam) r₀`, write `D := dilatedDomainCd Ω lam` and
`w := dilateWideCd u ∈ H¹(D)` (so `approxCvx u lam ε = mollifier ε ⋆ extCd w`, definitionally).

* **Step 0** (`closedBall_subset_dilatedDomain_acx`): a geometric convexity argument shows every
  `x ∈ closure Ω` has `closedBall x ε ⊆ D`.
* **Step 1** (`integral_convex_conv_extCd_sub_sq_le_acx`): the mollification error of `w` on `Ω`
  is `≤ ε² dirichlet w`.  Since `w` need not be `C¹`, the proof goes through the `C¹` density
  theorem `RobinCaps.Sobolev.exists_smooth_close_cd` (applied on `D`): approximate `w` by a
  globally `C¹`, compactly supported `F` (mass/Dirichlet-close), apply `SmoothConvSetEst` to `F`,
  identify `ρ_ε ⋆ (D.indicator F) = ρ_ε ⋆ F` on `Ω` using Step 0, and let the approximation error
  `η → 0` via `le_of_forall_le_add_mul_sqrt`, using a Minkowski inequality for `dirichlet`
  (`sqrt_integral_norm_sub_sq_le_add_acx`, the vector-valued analogue of
  `sqrt_integral_sub_sq_le_add_measure`, built from `dist_toLp_sq_gen`).
* **Step 2** (`integral_convex_ext_dilate_sub_sq_le_acx`): the dilation error of `u` on `Ω` is
  `≤ (1-lam)² ρ₀² 2ⁿ dirichlet u`.  Same density scheme, this time approximating `u` on `Ω`
  itself and using `SmoothDilateSetEst` together with the change-of-variables formula
  `setIntegral_comp_smul` (`RobinCaps/Compact/Dilation.lean`).
* **Step 3** (`dirichlet_dilateWideCd_le_acx`): `dirichlet w ≤ 2ⁿ dirichlet u` by the exact
  change-of-variables computation (no density needed).
* **Step 4**: combine Steps 1-3 via the crude pointwise bound
  `(a-c)² ≤ 2(a-b)² + 2(b-c)²` (`a := approxCvx u lam ε x`, `b := u (lam x) = extCd w x`,
  `c := u x`), then `a² + b² ≤ (a+b)²`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak
open RobinCaps.Sobolev (extCd extCd_apply_of_mem extCd_apply_of_not_mem memLp_extCd
  dilatedDomainCd self_subset_dilatedDomain_cd isOpen_dilatedDomain_cd isBounded_dilatedDomain_cd
  dilateWideCd dilateWideCd_toFun dilateWideCd_grad star_shaped_cd exists_smooth_close_cd
  mass_sub_comm_cd)

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Two `L²` Minkowski-type helpers -/

/-- **Vector-valued Minkowski inequality** on a set `D`, built from `dist_toLp_sq_gen`. -/
theorem sqrt_integral_norm_sub_sq_le_add_acx {D : Set E} {f g h : E → E}
    (hf : MemLp f 2 (volume.restrict D)) (hg : MemLp g 2 (volume.restrict D))
    (hh : MemLp h 2 (volume.restrict D)) :
    Real.sqrt (∫ x in D, ‖f x - h x‖ ^ 2)
      ≤ Real.sqrt (∫ x in D, ‖f x - g x‖ ^ 2) + Real.sqrt (∫ x in D, ‖g x - h x‖ ^ 2) := by
  have e1 : Real.sqrt (∫ x in D, ‖f x - h x‖ ^ 2) = dist (hf.toLp f) (hh.toLp h) := by
    rw [← dist_toLp_sq_gen hf hh, Real.sqrt_sq dist_nonneg]
  have e2 : Real.sqrt (∫ x in D, ‖f x - g x‖ ^ 2) = dist (hf.toLp f) (hg.toLp g) := by
    rw [← dist_toLp_sq_gen hf hg, Real.sqrt_sq dist_nonneg]
  have e3 : Real.sqrt (∫ x in D, ‖g x - h x‖ ^ 2) = dist (hg.toLp g) (hh.toLp h) := by
    rw [← dist_toLp_sq_gen hg hh, Real.sqrt_sq dist_nonneg]
  rw [e1, e2, e3]
  exact dist_triangle _ _ _

/-- **Minkowski inequality for `dirichlet`.** -/
theorem sqrt_dirichlet_le_add_acx {D : Set E} (a b : H1 D) :
    Real.sqrt (dirichlet a) ≤ Real.sqrt (dirichlet (a - b)) + Real.sqrt (dirichlet b) := by
  have htri := sqrt_integral_norm_sub_sq_le_add_acx a.grad_memL2 b.grad_memL2
    (MemLp.zero (μ := volume.restrict D))
  simp only [Pi.zero_apply, sub_zero] at htri
  rw [dirichlet_sub]
  unfold dirichlet
  exact htri

/-! ## `extCd` is additive, and its squared integral is the mass -/

theorem extCd_sub_acx {D : Set E} (u v : H1 D) :
    extCd (u - v) = fun x => extCd u x - extCd v x := by
  funext x
  by_cases hx : x ∈ D
  · rw [extCd_apply_of_mem u hx, extCd_apply_of_mem v hx, extCd_apply_of_mem (u - v) hx,
      H1.sub_toFun, Pi.sub_apply]
  · rw [extCd_apply_of_not_mem u hx, extCd_apply_of_not_mem v hx,
      extCd_apply_of_not_mem (u - v) hx]
    ring

theorem integral_extCd_sq_acx {D : Set E} (hDmeas : MeasurableSet D) (v : H1 D) :
    ∫ x, extCd v x ^ 2 = mass v := by
  unfold mass
  rw [← integral_indicator hDmeas]
  congr 1
  funext x
  by_cases hx : x ∈ D
  · simp [extCd_apply_of_mem v hx, indicator_of_mem hx]
  · simp [extCd_apply_of_not_mem v hx, indicator_of_notMem hx]

theorem integral_extCd_sub_sq_eq_mass_acx {D : Set E} (hDmeas : MeasurableSet D) (u v : H1 D) :
    ∫ x, (extCd u x - extCd v x) ^ 2 = mass (u - v) := by
  rw [← integral_extCd_sq_acx hDmeas (u - v)]
  congr 1
  funext x
  rw [extCd_sub_acx]

/-! ## Step 0: the geometric gap -/

/-- **Step 0.**  For `Ω` bounded convex open with `ball 0 r₀ ⊆ Ω`, `1/2 ≤ lam < 1` and
`0 < ε < (1-lam) r₀`, every `x ∈ closure Ω` has `closedBall x ε ⊆ dilatedDomainCd Ω lam`. -/
theorem closedBall_subset_dilatedDomain_acx {Ω : Set E} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hball : ball (0 : E) r₀ ⊆ Ω) {lam ε : ℝ} (hlam : 1 / 2 ≤ lam)
    (hlam1 : lam < 1) (hε : 0 < ε) (hε' : ε < (1 - lam) * r₀) :
    ∀ x ∈ closure Ω, closedBall x ε ⊆ dilatedDomainCd Ω lam := by
  intro x hx y hy
  show lam • y ∈ Ω
  have hlam0 : 0 ≤ lam := by linarith
  have h1lam : 0 < 1 - lam := by linarith
  set z : E := (lam / (1 - lam)) • (y - x) with hzdef
  have hcomb : lam • x + (1 - lam) • z = lam • y := by
    have hs : (1 - lam) • z = lam • (y - x) := by
      rw [hzdef, smul_smul]
      congr 1
      field_simp
    rw [hs, smul_sub]
    abel
  have hdist : ‖y - x‖ ≤ ε := by
    rw [mem_closedBall, dist_eq_norm] at hy
    simpa using hy
  have hzr0 : ‖z‖ < r₀ := by
    rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam / (1 - lam))]
    have hlt : lam / (1 - lam) * ‖y - x‖ ≤ lam / (1 - lam) * ε :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    have heq2 : lam / (1 - lam) * ε < r₀ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ h1lam]
      nlinarith
    linarith
  have hzInt : z ∈ interior Ω := by
    have hzball : z ∈ ball (0 : E) r₀ := by rw [mem_ball, dist_zero_right]; exact hzr0
    have hzΩ : z ∈ Ω := hball hzball
    rwa [hopen.interior_eq]
  have hmem : lam • x + (1 - lam) • z ∈ interior Ω :=
    hconv.combo_closure_interior_mem_interior hx hzInt hlam0 h1lam (by ring)
  rw [hcomb] at hmem
  exact interior_subset hmem

/-! ## Step 3: the Dirichlet energy of the wide dilation -/

/-- **Step 3.**  `dirichlet (dilateWideCd u) ≤ 2ⁿ dirichlet u`. -/
theorem dirichlet_dilateWideCd_le_acx {Ω : Set E} (hΩmeas : MeasurableSet Ω) (u : H1 Ω)
    {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) (hlam0 : 0 < lam) :
    dirichlet (dilateWideCd hΩmeas u hlam0) ≤ 2 ^ n * dirichlet u := by
  have hDmeas' : MeasurableSet (dilatedDomainCd Ω lam) := hΩmeas.preimage (measurable_const_smul lam)
  have hpt : ∀ x : E, ‖(dilateWideCd hΩmeas u hlam0).grad x‖ ^ 2 = lam ^ 2 * ‖u.grad (lam • x)‖ ^ 2 := by
    intro x
    rw [dilateWideCd_grad, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have heq1 : dirichlet (dilateWideCd hΩmeas u hlam0)
      = lam ^ 2 * ∫ x in dilatedDomainCd Ω lam, ‖u.grad (lam • x)‖ ^ 2 := by
    unfold dirichlet
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hDmeas' fun x _ => hpt x
  have heq2 : (∫ x in dilatedDomainCd Ω lam, ‖u.grad (lam • x)‖ ^ 2) = (lam ^ n)⁻¹ * dirichlet u :=
    setIntegral_comp_smul hlam0 hΩmeas (fun y => ‖u.grad y‖ ^ 2)
  rw [heq1, heq2]
  have h1 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam0.le hlam1
  have h2 : lam⁻¹ ^ n ≤ 2 ^ n := inv_pow_le_two_pow hlam
  have hD0 : 0 ≤ dirichlet u := dirichlet_nonneg u
  calc lam ^ 2 * ((lam ^ n)⁻¹ * dirichlet u) = lam ^ 2 * lam⁻¹ ^ n * dirichlet u := by
        rw [inv_pow]; ring
    _ ≤ 1 * 2 ^ n * dirichlet u := by gcongr
    _ = 2 ^ n * dirichlet u := by ring

/-! ## Step 1: the mollification error on a general convex domain -/

/-- **Step 1.**  For `D` bounded convex open with `0 ∈ D`, `w ∈ H¹(D)`, `Ω` bounded measurable
with the uniform gap `∀ x ∈ closure Ω, closedBall x ε ⊆ D`, the mollification error of `w` on
`Ω` is `≤ ε² dirichlet w`. -/
theorem integral_convex_conv_extCd_sub_sq_le_acx (hn : 0 < n) {D : Set E} (hDconv : Convex ℝ D)
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (h0D : (0 : E) ∈ D) (w : H1 D)
    {Ω : Set E} (hΩmeas : MeasurableSet Ω) (hΩbdd : Bornology.IsBounded Ω) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ x ∈ closure Ω, closedBall x ε ⊆ D) (hS : SmoothConvSetEst n) :
    ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
        - extCd w x) ^ 2 ≤ ε ^ 2 * dirichlet w := by
  have hDmeas : MeasurableSet D := hDopen.measurableSet
  have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
  have hw2 : MemLp (extCd w) 2 volume := memLp_extCd w hDmeas
  have hD0 : 0 ≤ dirichlet w := dirichlet_nonneg w
  have hρw : MemLp (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) 2 volume :=
    memLp_conv hρ hw2
  have hA0 : 0 ≤ ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      extCd w) x - extCd w x) ^ 2 := setIntegral_sub_sq_nonneg _ _ _
  have key : ∀ η : ℝ, 0 < η →
      Real.sqrt (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          extCd w) x - extCd w x) ^ 2)
        ≤ ε * Real.sqrt (dirichlet w) + (ε + 2) * Real.sqrt η := by
    intro η hη
    obtain ⟨Fu, hFu, hFuc, hclose⟩ := exists_smooth_close_cd hn hDconv hDopen hDbdd h0D w hη
    set wF : H1 D := H1.ofCompactSupport D Fu hFu hFuc with hwFdef
    have hFuL2 : MemLp Fu 2 volume := hFu.continuous.memLp_of_hasCompactSupport hFuc
    have hmassle : mass (wF - w) ≤ η := by
      have hd : 0 ≤ dirichlet (wF - w) := dirichlet_nonneg _
      linarith [hclose]
    -- T1: contraction bound, whole space then restrict.
    have hT1 : ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        extCd w) x - (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        extCd wF) x) ^ 2 ≤ η := by
      have hint : Integrable (fun x => ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          volume] extCd w) x - (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          extCd wF) x) ^ 2) volume :=
        (hρw.sub (memLp_conv hρ (memLp_extCd wF hDmeas))).integrable_sq
      calc ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
            - (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd wF) x) ^ 2
          ≤ ∫ x, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
              - (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd wF) x) ^ 2 :=
            setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)
        _ ≤ ∫ x, (extCd w x - extCd wF x) ^ 2 :=
            integral_conv_sub_sq_le hρ hw2 (memLp_extCd wF hDmeas)
        _ = mass (w - wF) := integral_extCd_sub_sq_eq_mass_acx hDmeas w wF
        _ = mass (wF - w) := mass_sub_comm_cd w wF
        _ ≤ η := hmassle
    -- T2: hS applied to `Fu`, after identifying the convolutions on `Ω`.
    have hpteq : ∀ x ∈ Ω, (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        extCd wF) x = (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Fu) x := by
      intro x hx
      rw [IsMollifier.conv_apply (extCd wF) x, IsMollifier.conv_apply Fu x]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      by_cases ht : mollifier (n := n) ε t = 0
      · simp [ht]
      · have htε : ‖t‖ ≤ ε := by
          by_contra hcon
          exact ht (hρ.eq_zero_of_lt_norm (lt_of_not_ge hcon))
        have hxt : x - t ∈ D := by
          refine hgap x (subset_closure hx) ?_
          rw [mem_closedBall, dist_eq_norm]
          simpa using htε
        show mollifier (n := n) ε t * extCd wF (x - t) = mollifier (n := n) ε t * Fu (x - t)
        rw [extCd_apply_of_mem wF hxt, H1.ofCompactSupport_toFun]
    have hxD : ∀ x ∈ Ω, x ∈ D := fun x hx =>
      hgap x (subset_closure hx) (mem_closedBall_self hε.le)
    have hT2eq : Set.EqOn (fun x => ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] extCd wF) x - extCd wF x) ^ 2)
        (fun x => ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Fu) x
          - Fu x) ^ 2) Ω := by
      intro x hx
      simp only
      rw [hpteq x hx, extCd_apply_of_mem wF (hxD x hx), H1.ofCompactSupport_toFun]
    have hSest : ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Fu) x
          - Fu x) ^ 2
        ≤ ε ^ 2 * ∫ x in cthickening ε Ω, ‖fderiv ℝ Fu x‖ ^ 2 :=
      hS ε (mollifier (n := n) ε) hρ hε.le Fu hFu Ω hΩmeas hΩbdd
    have hcthick : cthickening ε Ω ⊆ D := by
      rw [cthickening_eq_biUnion_closedBall Ω hε.le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      exact hgap y hy hyx
    have hgradcont : Continuous (fun x => ‖fderiv ℝ Fu x‖ ^ 2) :=
      ((hFu.continuous_fderiv le_rfl).norm).pow 2
    have hgradcs : HasCompactSupport (fun x => ‖fderiv ℝ Fu x‖ ^ 2) :=
      (hFuc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => ‖L‖ ^ 2) (by simp)
    have hgradInt : Integrable (fun x => ‖fderiv ℝ Fu x‖ ^ 2) volume :=
      hgradcont.integrable_of_hasCompactSupport hgradcs
    have hcthickMono : ∫ x in cthickening ε Ω, ‖fderiv ℝ Fu x‖ ^ 2
        ≤ ∫ x in D, ‖fderiv ℝ Fu x‖ ^ 2 :=
      setIntegral_mono_set hgradInt.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        hcthick.eventuallyLE
    have hDdirichlet : (∫ x in D, ‖fderiv ℝ Fu x‖ ^ 2) = dirichlet wF := by
      unfold dirichlet
      rw [H1.ofCompactSupport_grad]
      refine setIntegral_congr_fun hDmeas fun x _ => ?_
      rw [norm_fderiv_eq_norm_classicalGrad]
    have hT2 : ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        extCd wF) x - extCd wF x) ^ 2 ≤ ε ^ 2 * dirichlet wF := by
      rw [setIntegral_congr_fun hΩmeas hT2eq]
      calc ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Fu) x
            - Fu x) ^ 2
          ≤ ε ^ 2 * ∫ x in cthickening ε Ω, ‖fderiv ℝ Fu x‖ ^ 2 := hSest
        _ ≤ ε ^ 2 * ∫ x in D, ‖fderiv ℝ Fu x‖ ^ 2 := by gcongr
        _ = ε ^ 2 * dirichlet wF := by rw [hDdirichlet]
    -- T3: direct mass bound.
    have hT3 : ∫ x in Ω, (extCd wF x - extCd w x) ^ 2 ≤ η := by
      have hint : Integrable (fun x => (extCd wF x - extCd w x) ^ 2) volume :=
        ((memLp_extCd wF hDmeas).sub hw2).integrable_sq
      calc ∫ x in Ω, (extCd wF x - extCd w x) ^ 2
          ≤ ∫ x, (extCd wF x - extCd w x) ^ 2 :=
            setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)
        _ = mass (wF - w) := integral_extCd_sub_sq_eq_mass_acx hDmeas wF w
        _ ≤ η := hmassle
    -- Combine via two triangle-inequality steps.
    have hdirWF : Real.sqrt (dirichlet wF) ≤ Real.sqrt (dirichlet w) + Real.sqrt η := by
      have htri := sqrt_dirichlet_le_add_acx wF w
      have hdWFw : dirichlet (wF - w) ≤ η := by
        have hmn : 0 ≤ mass (wF - w) := mass_nonneg _
        linarith [hclose]
      calc Real.sqrt (dirichlet wF) ≤ Real.sqrt (dirichlet (wF - w)) + Real.sqrt (dirichlet w) := htri
        _ ≤ Real.sqrt η + Real.sqrt (dirichlet w) := by gcongr
        _ = Real.sqrt (dirichlet w) + Real.sqrt η := by ring
    calc Real.sqrt (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          extCd w) x - extCd w x) ^ 2)
        ≤ Real.sqrt (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd w) x - (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd wF) x) ^ 2)
          + Real.sqrt (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd wF) x - extCd w x) ^ 2) :=
          sqrt_integral_sub_sq_le_add_measure (hρw.restrict Ω)
            ((memLp_conv hρ (memLp_extCd wF hDmeas)).restrict Ω) (hw2.restrict Ω)
      _ ≤ Real.sqrt (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd w) x - (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd wF) x) ^ 2)
          + (Real.sqrt (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd wF) x - extCd wF x) ^ 2)
            + Real.sqrt (∫ x in Ω, (extCd wF x - extCd w x) ^ 2)) :=
          add_le_add le_rfl
            (sqrt_integral_sub_sq_le_add_measure ((memLp_conv hρ (memLp_extCd wF hDmeas)).restrict Ω)
              ((memLp_extCd wF hDmeas).restrict Ω) (hw2.restrict Ω))
      _ ≤ Real.sqrt η + (Real.sqrt (ε ^ 2 * dirichlet wF) + Real.sqrt η) :=
          add_le_add (Real.sqrt_le_sqrt hT1)
            (add_le_add (Real.sqrt_le_sqrt hT2) (Real.sqrt_le_sqrt hT3))
      _ ≤ Real.sqrt η + (ε * (Real.sqrt (dirichlet w) + Real.sqrt η) + Real.sqrt η) := by
          have hDF0 : 0 ≤ dirichlet wF := dirichlet_nonneg wF
          have heqsqrt : Real.sqrt (ε ^ 2 * dirichlet wF) = ε * Real.sqrt (dirichlet wF) := by
            rw [Real.sqrt_mul' _ hDF0, Real.sqrt_sq hε.le]
          rw [heqsqrt]
          gcongr
      _ = ε * Real.sqrt (dirichlet w) + (ε + 2) * Real.sqrt η := by ring
  have hsqrt := le_of_forall_le_add_mul_sqrt (by positivity) key
  refine le_of_sqrt_le_sqrt hA0 (by positivity) ?_
  rw [Real.sqrt_mul' _ hD0, Real.sqrt_sq hε.le]
  exact hsqrt

/-! ## Step 2: the dilation error on a general convex domain -/

/-- **Step 2.**  For `Ω` bounded convex open with `0 ∈ Ω`, `∀ x ∈ Ω, ‖x‖ ≤ ρ₀`, `u ∈ H¹(Ω)` and
`1/2 ≤ lam ≤ 1`, the dilation error is `≤ (1-lam)² ρ₀² 2ⁿ dirichlet u`. -/
theorem integral_convex_ext_dilate_sub_sq_le_acx (hn : 0 < n) {Ω : Set E} (hconv : Convex ℝ Ω)
    (hopen : IsOpen Ω) (hbdd : Bornology.IsBounded Ω) (h0 : (0 : E) ∈ Ω) (u : H1 Ω)
    {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hΩρ : ∀ x ∈ Ω, ‖x‖ ≤ ρ₀) {lam : ℝ} (hlam : 1 / 2 ≤ lam)
    (hlam1 : lam ≤ 1) (hD : SmoothDilateSetEst n) :
    ∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2 ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet u := by
  have hΩmeas : MeasurableSet Ω := hopen.measurableSet
  have hlam0 : 0 < lam := by linarith
  have hD'sub : Ω ⊆ dilatedDomainCd Ω lam := self_subset_dilatedDomain_cd hconv h0 hlam0.le hlam1
  have hD'meas : MeasurableSet (dilatedDomainCd Ω lam) := hΩmeas.preimage (measurable_const_smul lam)
  have hu2 : MemLp u.toFun 2 (volume.restrict Ω) := u.memL2
  have hg1 : MemLp (fun x => u.toFun (lam • x)) 2 (volume.restrict Ω) :=
    (memLp_comp_smul_restrict hlam0 hΩmeas u.memL2).mono_measure (Measure.restrict_mono hD'sub le_rfl)
  have hA0 : 0 ≤ ∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hC0 : 0 ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet u :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg (1 - lam)) (sq_nonneg ρ₀))
      (by positivity : (0:ℝ) ≤ 2 ^ n)) (dirichlet_nonneg u)
  have hlamρ0 : 0 ≤ (1 - lam) * ρ₀ := mul_nonneg (by linarith) hρ₀
  have key : ∀ η : ℝ, 0 < η →
      Real.sqrt (∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2)
        ≤ (1 - lam) * ρ₀ * Real.sqrt (2 ^ n) * Real.sqrt (dirichlet u)
          + (Real.sqrt (2 ^ n) + (1 - lam) * ρ₀ * Real.sqrt (2 ^ n) + 1) * Real.sqrt η := by
    intro η hη
    obtain ⟨Fu, hFu, hFuc, hclose⟩ := exists_smooth_close_cd hn hconv hopen hbdd h0 u hη
    set uF : H1 Ω := H1.ofCompactSupport Ω Fu hFu hFuc with huFdef
    have hFuL2 : MemLp Fu 2 volume := hFu.continuous.memLp_of_hasCompactSupport hFuc
    have hmassle : mass (uF - u) ≤ η := by
      have hd : 0 ≤ dirichlet (uF - u) := dirichlet_nonneg _
      linarith [hclose]
    -- T1: change of variables for `g := u.toFun - Fu`.
    have hgΩ : MemLp (fun x => u.toFun x - Fu x) 2 (volume.restrict Ω) := hu2.sub (hFuL2.restrict Ω)
    have hgD' : MemLp (fun x => u.toFun (lam • x) - Fu (lam • x)) 2
        (volume.restrict (dilatedDomainCd Ω lam)) := memLp_comp_smul_restrict hlam0 hΩmeas hgΩ
    have hT1 : ∫ x in Ω, (u.toFun (lam • x) - Fu (lam • x)) ^ 2 ≤ 2 ^ n * η := by
      have hT1eq : (∫ x in dilatedDomainCd Ω lam, (u.toFun (lam • x) - Fu (lam • x)) ^ 2)
          = (lam ^ n)⁻¹ * ∫ y in Ω, (u.toFun y - Fu y) ^ 2 :=
        setIntegral_comp_smul hlam0 hΩmeas (fun y => (u.toFun y - Fu y) ^ 2)
      have hmono : ∫ x in Ω, (u.toFun (lam • x) - Fu (lam • x)) ^ 2
          ≤ ∫ x in dilatedDomainCd Ω lam, (u.toFun (lam • x) - Fu (lam • x)) ^ 2 :=
        setIntegral_mono_set hgD'.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
          hD'sub.eventuallyLE
      have h2n : lam⁻¹ ^ n ≤ 2 ^ n := inv_pow_le_two_pow hlam
      have hgnn : 0 ≤ ∫ y in Ω, (u.toFun y - Fu y) ^ 2 := integral_nonneg fun _ => sq_nonneg _
      calc ∫ x in Ω, (u.toFun (lam • x) - Fu (lam • x)) ^ 2
          ≤ ∫ x in dilatedDomainCd Ω lam, (u.toFun (lam • x) - Fu (lam • x)) ^ 2 := hmono
        _ = (lam ^ n)⁻¹ * ∫ y in Ω, (u.toFun y - Fu y) ^ 2 := hT1eq
        _ = lam⁻¹ ^ n * ∫ y in Ω, (u.toFun y - Fu y) ^ 2 := by rw [inv_pow]
        _ ≤ 2 ^ n * ∫ y in Ω, (u.toFun y - Fu y) ^ 2 := mul_le_mul_of_nonneg_right h2n hgnn
        _ = 2 ^ n * mass (u - uF) := by
              rw [mass_sub]; simp only [huFdef, H1.ofCompactSupport_toFun]
        _ = 2 ^ n * mass (uF - u) := by rw [mass_sub_comm_cd u uF]
        _ ≤ 2 ^ n * η := by
            have h2npos : (0:ℝ) ≤ 2 ^ n := by positivity
            exact mul_le_mul_of_nonneg_left hmassle h2npos
    -- T2: `SmoothDilateSetEst` applied to `Fu`.
    have hstar : ∀ x ∈ Ω, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s • x ∈ Ω :=
      fun x hx s hs0 hs1 => star_shaped_cd hconv h0 hx hs0 hs1
    have hDest : ∫ x in Ω, (Fu (lam • x) - Fu x) ^ 2
        ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * ∫ x in Ω, ‖fderiv ℝ Fu x‖ ^ 2 :=
      hD Fu hFu Ω hΩmeas hbdd hstar ρ₀ hρ₀ hΩρ lam hlam hlam1
    have hgradEq : (∫ x in Ω, ‖fderiv ℝ Fu x‖ ^ 2) = dirichlet uF := by
      unfold dirichlet
      rw [H1.ofCompactSupport_grad]
      refine setIntegral_congr_fun hΩmeas fun x _ => ?_
      rw [norm_fderiv_eq_norm_classicalGrad]
    have hT2 : ∫ x in Ω, (Fu (lam • x) - Fu x) ^ 2 ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet uF := by
      rw [← hgradEq]; exact hDest
    -- T3: direct mass bound.
    have hT3 : ∫ x in Ω, (Fu x - u.toFun x) ^ 2 ≤ η := by
      have heq : (∫ x in Ω, (Fu x - u.toFun x) ^ 2) = mass (uF - u) := (mass_sub uF u).symm
      rw [heq]; exact hmassle
    -- The Minkowski inequality for `dirichlet uF`.
    have hdiruF : Real.sqrt (dirichlet uF) ≤ Real.sqrt (dirichlet u) + Real.sqrt η := by
      have htri := sqrt_dirichlet_le_add_acx uF u
      have hduFu : dirichlet (uF - u) ≤ η := by
        have hmn : 0 ≤ mass (uF - u) := mass_nonneg _
        linarith [hclose]
      calc Real.sqrt (dirichlet uF) ≤ Real.sqrt (dirichlet (uF - u)) + Real.sqrt (dirichlet u) := htri
        _ ≤ Real.sqrt η + Real.sqrt (dirichlet u) := by gcongr
        _ = Real.sqrt (dirichlet u) + Real.sqrt η := by ring
    have hFuL2Ω : MemLp Fu 2 (volume.restrict Ω) := hFuL2.restrict Ω
    -- Combine via two triangle-inequality steps.
    calc Real.sqrt (∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2)
        ≤ Real.sqrt (∫ x in Ω, (u.toFun (lam • x) - Fu (lam • x)) ^ 2)
          + Real.sqrt (∫ x in Ω, (Fu (lam • x) - u.toFun x) ^ 2) :=
          sqrt_integral_sub_sq_le_add_measure hg1
            (memLp_comp_smul_restrict hlam0 hΩmeas hFuL2Ω |>.mono_measure
              (Measure.restrict_mono hD'sub le_rfl)) hu2
      _ ≤ Real.sqrt (∫ x in Ω, (u.toFun (lam • x) - Fu (lam • x)) ^ 2)
          + (Real.sqrt (∫ x in Ω, (Fu (lam • x) - Fu x) ^ 2)
            + Real.sqrt (∫ x in Ω, (Fu x - u.toFun x) ^ 2)) :=
          add_le_add le_rfl
            (sqrt_integral_sub_sq_le_add_measure
              (memLp_comp_smul_restrict hlam0 hΩmeas hFuL2Ω |>.mono_measure
                (Measure.restrict_mono hD'sub le_rfl)) hFuL2Ω hu2)
      _ ≤ Real.sqrt (2 ^ n * η)
          + (Real.sqrt ((1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet uF) + Real.sqrt η) :=
          add_le_add (Real.sqrt_le_sqrt hT1)
            (add_le_add (Real.sqrt_le_sqrt hT2) (Real.sqrt_le_sqrt hT3))
      _ ≤ Real.sqrt (2 ^ n) * Real.sqrt η
          + ((1 - lam) * ρ₀ * Real.sqrt (2 ^ n) * (Real.sqrt (dirichlet u) + Real.sqrt η)
            + Real.sqrt η) := by
          have h2n0 : (0:ℝ) ≤ 2 ^ n := by positivity
          have heq1 : Real.sqrt (2 ^ n * η) = Real.sqrt (2 ^ n) * Real.sqrt η := Real.sqrt_mul h2n0 η
          have hDuF0 : 0 ≤ dirichlet uF := dirichlet_nonneg uF
          have heq2 : Real.sqrt ((1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet uF)
              = (1 - lam) * ρ₀ * Real.sqrt (2 ^ n) * Real.sqrt (dirichlet uF) := by
            rw [show (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet uF
              = ((1 - lam) * ρ₀) ^ 2 * (2 ^ n * dirichlet uF) by ring,
              Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith),
              Real.sqrt_mul h2n0]
            ring
          rw [heq1, heq2]
          have := mul_le_mul_of_nonneg_left hdiruF
            (by positivity : (0:ℝ) ≤ (1 - lam) * ρ₀ * Real.sqrt (2 ^ n))
          linarith
      _ = (1 - lam) * ρ₀ * Real.sqrt (2 ^ n) * Real.sqrt (dirichlet u)
          + (Real.sqrt (2 ^ n) + (1 - lam) * ρ₀ * Real.sqrt (2 ^ n) + 1) * Real.sqrt η := by ring
  have hsqrt := le_of_forall_le_add_mul_sqrt (by positivity) key
  refine le_of_sqrt_le_sqrt hA0 hC0 ?_
  have heqC : Real.sqrt ((1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet u)
      = (1 - lam) * ρ₀ * Real.sqrt (2 ^ n) * Real.sqrt (dirichlet u) := by
    have hDu0 : 0 ≤ dirichlet u := dirichlet_nonneg u
    have h2n0 : (0:ℝ) ≤ 2 ^ n := by positivity
    rw [show (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet u
        = ((1 - lam) * ρ₀) ^ 2 * (2 ^ n * dirichlet u) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hlamρ0, Real.sqrt_mul h2n0]
    ring
  rw [heqC]
  exact hsqrt

/-! ## Step 4: combination -/

/-- **(A1) on a convex domain.** -/
theorem approxEstimateCvx_acx {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    {r₀ ρ₀ : ℝ} (hr₀ : 0 < r₀) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₀ ⊆ Ω)
    (hρ₀ : 0 ≤ ρ₀) (hΩρ : ∀ x ∈ Ω, ‖x‖ ≤ ρ₀)
    (hS : SmoothConvSetEst n) (hD : SmoothDilateSetEst n) :
    ApproxEstimateCvx Ω r₀ ρ₀ := by
  intro u lam ε hlam hlam1 hε hε'
  have hΩmeas : MeasurableSet Ω := hopen.measurableSet
  have hlam0 : 0 < lam := by linarith
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω := hball (mem_ball_self hr₀)
  set D : Set (EuclideanSpace ℝ (Fin n)) := dilatedDomainCd Ω lam with hDdef
  set w : H1 D := dilateWideCd hΩmeas u hlam0 with hwdef
  have hDconv : Convex ℝ D := hconv.is_linear_preimage (IsLinearMap.isLinearMap_smul lam)
  have hDopen : IsOpen D := isOpen_dilatedDomain_cd hopen lam
  have hDbdd : Bornology.IsBounded D := isBounded_dilatedDomain_cd hbdd hlam0.ne'
  have h0D : (0 : EuclideanSpace ℝ (Fin n)) ∈ D := by
    show lam • (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω
    simpa using h0
  have hΩsubD : Ω ⊆ D := self_subset_dilatedDomain_cd hconv h0 hlam0.le hlam1.le
  have hgap0 : ∀ x ∈ closure Ω, closedBall x ε ⊆ D :=
    closedBall_subset_dilatedDomain_acx hconv hopen hr₀ hball hlam hlam1 hε hε'
  -- Step 1 + Step 3.
  have hStep1 : ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      extCd w) x - extCd w x) ^ 2 ≤ ε ^ 2 * dirichlet w :=
    integral_convex_conv_extCd_sub_sq_le_acx hn hDconv hDopen hDbdd h0D w hΩmeas hbdd hε hgap0 hS
  have hStep3 : dirichlet w ≤ 2 ^ n * dirichlet u :=
    dirichlet_dilateWideCd_le_acx hΩmeas u hlam hlam1.le hlam0
  have hDu0 : 0 ≤ dirichlet u := dirichlet_nonneg u
  have hSD : ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      extCd w) x - extCd w x) ^ 2 ≤ ε ^ 2 * (2 ^ n * dirichlet u) := by
    have h2n0 : (0:ℝ) ≤ ε ^ 2 := sq_nonneg _
    calc ∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
          - extCd w x) ^ 2 ≤ ε ^ 2 * dirichlet w := hStep1
      _ ≤ ε ^ 2 * (2 ^ n * dirichlet u) := mul_le_mul_of_nonneg_left hStep3 h2n0
  -- Step 2.
  have hStep2 : ∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2
      ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet u :=
    integral_convex_ext_dilate_sub_sq_le_acx hn hconv hopen hbdd h0 u hρ₀ hΩρ hlam hlam1.le hD
  -- Step 4: pointwise combination.
  have happrox : approxCvx u lam ε = mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      extCd w := approxCvx_eq_extCd hΩmeas u hlam0 ε
  have hkey : ∀ x ∈ Ω, (approxCvx u lam ε x - u.toFun x) ^ 2
      ≤ 2 * ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
          - extCd w x) ^ 2
        + 2 * (u.toFun (lam • x) - u.toFun x) ^ 2 := by
    intro x hx
    have hxD : x ∈ D := hΩsubD hx
    have heq2 : extCd w x = u.toFun (lam • x) := by
      rw [extCd_apply_of_mem w hxD, hwdef, dilateWideCd_toFun]
    have heq1 : approxCvx u lam ε x = (mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] extCd w) x := by rw [happrox]
    rw [heq1, heq2]
    nlinarith [sq_nonneg ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
      - 2 * u.toFun (lam • x) + u.toFun x)]
  have hInt1 : IntegrableOn (fun x => ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] extCd w) x - extCd w x) ^ 2) Ω volume := by
    have hDmeas : MeasurableSet D := hDopen.measurableSet
    have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
    have h := ((memLp_conv hρ (memLp_extCd w hDmeas)).sub (memLp_extCd w hDmeas)).integrable_sq
    simpa [Pi.sub_apply] using h.integrableOn
  have hInt2 : IntegrableOn (fun x => (u.toFun (lam • x) - u.toFun x) ^ 2) Ω volume := by
    have hD'sub : Ω ⊆ D := hΩsubD
    have hg1 : MemLp (fun x => u.toFun (lam • x)) 2 (volume.restrict Ω) :=
      (memLp_comp_smul_restrict hlam0 hΩmeas u.memL2).mono_measure (Measure.restrict_mono hD'sub le_rfl)
    have h := (hg1.sub u.memL2).integrable_sq
    simpa [Pi.sub_apply] using h
  have hIntTarget : IntegrableOn (fun x => (approxCvx u lam ε x - u.toFun x) ^ 2) Ω volume := by
    have hDmeas : MeasurableSet D := hDopen.measurableSet
    have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
    have hmemA : MemLp (approxCvx u lam ε) 2 volume := by
      rw [happrox]; exact memLp_conv hρ (memLp_extCd w hDmeas)
    have h := ((hmemA.restrict Ω).sub u.memL2).integrable_sq
    simpa [Pi.sub_apply] using h
  have hIntRHS : IntegrableOn (fun x => 2 * ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] extCd w) x - extCd w x) ^ 2 + 2 * (u.toFun (lam • x) - u.toFun x) ^ 2) Ω volume :=
    (hInt1.const_mul 2).add (hInt2.const_mul 2)
  have hfinal : ∫ x in Ω, (approxCvx u lam ε x - u.toFun x) ^ 2
      ≤ ∫ x in Ω, (2 * ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
          - extCd w x) ^ 2 + 2 * (u.toFun (lam • x) - u.toFun x) ^ 2) :=
    setIntegral_mono_on hIntTarget hIntRHS hΩmeas hkey
  have heqRHS : (∫ x in Ω, (2 * ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      extCd w) x - extCd w x) ^ 2 + 2 * (u.toFun (lam • x) - u.toFun x) ^ 2))
      = 2 * (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
          - extCd w x) ^ 2) + 2 * ∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2 := by
    rw [integral_add (hInt1.const_mul 2) (hInt2.const_mul 2), integral_const_mul, integral_const_mul]
  rw [heqRHS] at hfinal
  have hcross : 0 ≤ ε * ((1 - lam) * ρ₀) := mul_nonneg hε.le (mul_nonneg (by linarith) hρ₀)
  calc ∫ x in Ω, (approxCvx u lam ε x - u.toFun x) ^ 2
      ≤ 2 * (∫ x in Ω, ((mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd w) x
          - extCd w x) ^ 2) + 2 * ∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2 := hfinal
    _ ≤ 2 * (ε ^ 2 * (2 ^ n * dirichlet u)) + 2 * ((1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * dirichlet u) := by
        gcongr
    _ = 2 ^ (n + 1) * (ε ^ 2 + (1 - lam) ^ 2 * ρ₀ ^ 2) * dirichlet u := by ring
    _ ≤ 2 ^ (n + 1) * (ε + (1 - lam) * ρ₀) ^ 2 * dirichlet u := by
        have hle : ε ^ 2 + (1 - lam) ^ 2 * ρ₀ ^ 2 ≤ (ε + (1 - lam) * ρ₀) ^ 2 := by nlinarith [hcross]
        have h2n1 : (0:ℝ) ≤ 2 ^ (n + 1) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle h2n1) hDu0

end RobinCaps.Compact

end
