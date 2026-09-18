import RobinCaps.Compact.GradCalc
import RobinCaps.Compact.PiconePointwise
import RobinCaps.Compact.RadialFun
import RobinCaps.Compact.DivergenceBall
import RobinCaps.Compact.BoundaryNonneg
import RobinCaps.Compact.Minimiser
import RobinCaps.Compact.GroundStateGap

/-!
# The Picone inequality on the ball

This file proves the Picone comparison inequality for the Robin form on `B_R`, using an
explicit positive radial comparison function `ψ = radialFun g` solving the radial ODE
`4 s g'' + 2 n g' + ν g = 0` with a Robin-supersolution boundary condition.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open scoped InnerProductSpace ContDiff

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## A globally positive profile agreeing with `g` near `[0, R²]` -/

/-- A `C²` profile that is positive on `[0, R²]` can be replaced by a `C²` profile positive
everywhere that agrees with it on a neighbourhood of `[0, R²]`. -/
theorem exists_pos_profile {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hpos : ∀ s, 0 ≤ s → s ≤ R ^ 2 → 0 < g s) :
    ∃ g₁ : ℝ → ℝ, ContDiff ℝ 2 g₁ ∧ (∀ s, 0 < g₁ s) ∧
      ∃ δ > 0, ∀ s, -δ < s → s < R ^ 2 + δ → g₁ s = g s := by
  -- `g` is positive on a thickening of `Icc 0 R²`
  have hopen : IsOpen {s : ℝ | 0 < g s} := isOpen_lt continuous_const hg.continuous
  have hsub : Icc (0 : ℝ) (R ^ 2) ⊆ {s : ℝ | 0 < g s} := fun s hs => hpos s hs.1 hs.2
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := isCompact_Icc.exists_thickening_subset_open hopen hsub
  have hIooSub : Ioo (-δ₀) (R ^ 2 + δ₀) ⊆ Metric.thickening δ₀ (Icc (0 : ℝ) (R ^ 2)) := by
    intro s hs
    rw [Metric.mem_thickening_iff]
    rcases le_or_gt 0 s with h0 | h0
    · rcases le_or_gt s (R ^ 2) with h1 | h1
      · exact ⟨s, ⟨h0, h1⟩, by simpa using hδ₀pos⟩
      · refine ⟨R ^ 2, ⟨sq_nonneg R, le_refl _⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [hs.2]
    · refine ⟨0, ⟨le_refl _, sq_nonneg R⟩, ?_⟩
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      linarith [hs.1]
  have hpos' : ∀ s, -δ₀ < s → s < R ^ 2 + δ₀ → 0 < g s := fun s h1 h2 =>
    hδ₀sub (hIooSub ⟨h1, h2⟩)
  -- the smooth bump function centred at `R²/2`
  set c : ℝ := R ^ 2 / 2 with hc
  have hbumplt : (R ^ 2 / 2 + δ₀ / 2 : ℝ) < R ^ 2 / 2 + δ₀ := by linarith
  have hbumppos : (0 : ℝ) < R ^ 2 / 2 + δ₀ / 2 := by positivity
  let χ : ContDiffBump c :=
    { rIn := R ^ 2 / 2 + δ₀ / 2, rOut := R ^ 2 / 2 + δ₀, rIn_pos := hbumppos,
      rIn_lt_rOut := hbumplt }
  have hχC2 : ContDiff ℝ 2 χ := χ.contDiff
  set g₁ : ℝ → ℝ := fun s => χ s * g s + (1 - χ s) with hg1def
  have hg1C2 : ContDiff ℝ 2 g₁ := by
    have h1 : ContDiff ℝ 2 (fun s => χ s * g s) := hχC2.mul hg
    have h2 : ContDiff ℝ 2 (fun s => (1 : ℝ) - χ s) := contDiff_const.sub hχC2
    exact h1.add h2
  refine ⟨g₁, hg1C2, ?_, δ₀ / 2, by positivity, ?_⟩
  · intro s
    rcases eq_or_ne (χ s) 0 with h0 | h0
    · simp [hg1def, h0]
    · have hmemsupp : s ∈ Function.support χ := h0
      rw [χ.support_eq] at hmemsupp
      rw [Real.ball_eq_Ioo] at hmemsupp
      have hsIoo : s ∈ Ioo (-δ₀) (R ^ 2 + δ₀) := by
        constructor
        · have := hmemsupp.1; simp only [hc] at this; linarith
        · have := hmemsupp.2; simp only [hc] at this; linarith
      have hgspos : 0 < g s := hpos' s hsIoo.1 hsIoo.2
      have hχ0 : 0 ≤ χ s := χ.nonneg
      have hχ1 : χ s ≤ 1 := χ.le_one
      set m : ℝ := min (g s) 1 with hm
      have hm0 : 0 < m := lt_min hgspos one_pos
      have e1 : χ s * m ≤ χ s * g s := mul_le_mul_of_nonneg_left (min_le_left _ _) hχ0
      have e2 : (1 - χ s) * m ≤ (1 - χ s) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      have : g₁ s ≥ m := by simp only [hg1def]; nlinarith [e1, e2]
      linarith
  · intro s h1 h2
    have hmem : s ∈ Metric.closedBall c χ.rIn := by
      rw [Real.closedBall_eq_Icc]
      constructor
      · simp only [hc]; show R ^ 2 / 2 - (R ^ 2 / 2 + δ₀ / 2) ≤ s; linarith
      · simp only [hc]; show s ≤ R ^ 2 / 2 + (R ^ 2 / 2 + δ₀ / 2); linarith
    have hχ1 : χ s = 1 := χ.one_of_mem_closedBall hmem
    simp only [hg1def, hχ1]
    ring

/-! ## Green's identity for the radial function against a `C¹` test function -/

/-- Green's identity for the radial function against `w`, in the special case needed for the
Picone inequality. -/
theorem dirichlet_pairing_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) {ν : ℝ}
    (hode : ∀ s, 0 ≤ s → s < R ^ 2 → 4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s
      + ν * g s = 0)
    (w : E → ℝ) (hw : ContDiff ℝ 1 w) :
    ∫ x in ball (0 : E) R, ⟪classicalGrad (radialFun g) x, classicalGrad w x⟫_ℝ
      = (ν * ∫ x in ball (0 : E) R, radialFun g x * w x)
        + 2 * R * deriv g (R ^ 2) * sphereIntegral n R w := by
  -- the profile `s ↦ 2 * deriv g s` is `C¹`
  have hgd1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hgs : ContDiff ℝ 1 (fun s => 2 * deriv g s) := by
    have heq : (fun s => 2 * deriv g s) = (fun s => (2 : ℝ) • deriv g s) := rfl
    rw [heq]
    exact hgd1.const_smul (2 : ℝ)
  have hkC1 : ContDiff ℝ 1 (fun z : E => 2 * deriv g (‖z‖ ^ 2)) := contDiff_radialFun hgs
  have hk1 : ∀ x : E, DifferentiableAt ℝ (fun z : E => 2 * deriv g (‖z‖ ^ 2)) x :=
    fun x => hkC1.differentiable le_rfl x
  have hw1 : ∀ x : E, DifferentiableAt ℝ w x := fun x => hw.differentiable le_rfl x
  -- the field `h := k * w`
  set h : E → ℝ := fun z => 2 * deriv g (‖z‖ ^ 2) * w z with hhdef
  have hhC1 : ContDiff ℝ 1 h := hkC1.mul hw
  have hdiv := integral_ball_div_radial hn hR h hhC1
  -- pointwise expansion of `∇h`
  have hgradh : ∀ x : E, classicalGrad h x
      = (2 * deriv g (‖x‖ ^ 2)) • classicalGrad w x
        + w x • classicalGrad (fun z : E => 2 * deriv g (‖z‖ ^ 2)) x := by
    intro x
    exact classicalGrad_mul (hk1 x) (hw1 x)
  have hinnerh : ∀ x : E, ⟪x, classicalGrad h x⟫_ℝ
      = (2 * deriv g (‖x‖ ^ 2)) * ⟪x, classicalGrad w x⟫_ℝ
        + w x * ⟪x, classicalGrad (fun z : E => 2 * deriv g (‖z‖ ^ 2)) x⟫_ℝ := by
    intro x
    rw [hgradh x, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  -- the key pointwise identity on the ball
  have hpt : ∀ x : E, x ∈ ball (0 : E) R →
      ⟪classicalGrad (radialFun g) x, classicalGrad w x⟫_ℝ
        = ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ) + ν * (radialFun g x * w x) := by
    intro x hx
    have hxlt : ‖x‖ ^ 2 < R ^ 2 := by
      have h1 : ‖x‖ < R := mem_ball_zero_iff.1 hx
      exact pow_lt_pow_left₀ h1 (norm_nonneg x) two_ne_zero
    have hode_x := hode (‖x‖ ^ 2) (sq_nonneg _) hxlt
    have hdgr := div_grad_radialFun hg x
    have hkey : (n : ℝ) * (2 * deriv g (‖x‖ ^ 2))
        + ⟪x, classicalGrad (fun z : E => 2 * deriv g (‖z‖ ^ 2)) x⟫_ℝ
        = -ν * radialFun g x := by
      rw [hdgr]
      simp only [radialFun_apply]
      linarith [hode_x]
    have hzero : (n : ℝ) * (2 * deriv g (‖x‖ ^ 2))
        + ⟪x, classicalGrad (fun z : E => 2 * deriv g (‖z‖ ^ 2)) x⟫_ℝ + ν * radialFun g x
        = 0 := by rw [hkey]; ring
    have hgradpsi : classicalGrad (radialFun g) x = (2 * deriv g (‖x‖ ^ 2)) • x :=
      classicalGrad_radialFun' (hg.of_le (by norm_num)) x
    rw [hgradpsi, real_inner_smul_left, hinnerh x]
    simp only [hhdef]
    linear_combination (-(w x)) * hzero
  -- integrability
  have hIh : IntegrableOn (fun x : E => (n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ)
      (ball (0 : E) R) :=
    integrableOn_ball_of_continuous
      ((continuous_const.mul hhC1.continuous).add
        (continuous_id.inner (continuous_classicalGrad h hhC1))) R
  have hIgw : IntegrableOn (fun x : E => ν * (radialFun g x * w x)) (ball (0 : E) R) :=
    integrableOn_ball_of_continuous
      (continuous_const.mul ((continuous_radialFun hg.continuous).mul hw.continuous)) R
  -- integrate the pointwise identity
  have hintegral : ∫ x in ball (0 : E) R,
      ⟪classicalGrad (radialFun g) x, classicalGrad w x⟫_ℝ
      = (∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ))
        + ∫ x in ball (0 : E) R, ν * (radialFun g x * w x) := by
    rw [← integral_add hIh hIgw]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using hpt x hx
  rw [hintegral, hdiv, integral_const_mul]
  -- the sphere integral of `h` in terms of `w`
  have hsphereh : sphereIntegral n R h = 2 * deriv g (R ^ 2) * sphereIntegral n R w := by
    have hptsph : ∀ y : sphere (0 : E) 1, h (R • (y : E)) = 2 * deriv g (R ^ 2) * w (R • (y : E)) := by
      intro y
      have hnorm : ‖R • (y : E)‖ = R := norm_smul_sphere hR y
      show 2 * deriv g (‖R • (y : E)‖ ^ 2) * w (R • (y : E))
        = 2 * deriv g (R ^ 2) * w (R • (y : E))
      rw [hnorm]
    simp only [sphereIntegral, hptsph, integral_const_mul]
    ring
  rw [hsphereh]
  ring

/-! ## The Picone inequality for `C¹` test functions -/

/-- **Picone inequality for `C¹` test functions.** -/
theorem picone_ofC1 (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {α : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) {ν : ℝ}
    (hode : ∀ s, 0 ≤ s → s < R ^ 2 → 4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s
      + ν * g s = 0)
    (hpos : ∀ s, 0 ≤ s → s ≤ R ^ 2 → 0 < g s)
    (hrobin : 0 ≤ 2 * R * deriv g (R ^ 2) + α * g (R ^ 2))
    (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    ν * mass (ofC1 R v hv) ≤ dirichlet (ofC1 R v hv) + α * bdR n R (ofC1 R v hv) (ofC1 R v hv) := by
  obtain ⟨g₁, hg1C2, hg1pos, δ, hδpos, hδeq⟩ := exists_pos_profile hR hg hpos
  have hUopen : IsOpen (Ioo (-δ) (R ^ 2 + δ)) := isOpen_Ioo
  have hg1_agrees : Set.EqOn g₁ g (Ioo (-δ) (R ^ 2 + δ)) := fun s hs => hδeq s hs.1 hs.2
  have hg1_deriv_agrees : Set.EqOn (deriv g₁) (deriv g) (Ioo (-δ) (R ^ 2 + δ)) :=
    fun s hs => (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) hg1_agrees).deriv_eq
  have hg1_deriv2_agrees : Set.EqOn (deriv (deriv g₁)) (deriv (deriv g)) (Ioo (-δ) (R ^ 2 + δ)) :=
    fun s hs => (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) hg1_deriv_agrees).deriv_eq
  have hRmem : R ^ 2 ∈ Ioo (-δ) (R ^ 2 + δ) := ⟨by nlinarith [sq_nonneg R], by linarith⟩
  have heqR2 : g₁ (R ^ 2) = g (R ^ 2) := hg1_agrees hRmem
  have heqR2' : deriv g₁ (R ^ 2) = deriv g (R ^ 2) := hg1_deriv_agrees hRmem
  have hg1ode : ∀ s, 0 ≤ s → s < R ^ 2 →
      4 * s * deriv (deriv g₁) s + 2 * (n : ℝ) * deriv g₁ s + ν * g₁ s = 0 := by
    intro s hs0 hsR
    have hmem : s ∈ Ioo (-δ) (R ^ 2 + δ) := ⟨by linarith, by linarith⟩
    rw [hg1_deriv2_agrees hmem, hg1_deriv_agrees hmem, hg1_agrees hmem]
    exact hode s hs0 hsR
  have hψ1ne : ∀ z : E, radialFun g₁ z ≠ 0 := fun z => (hg1pos _).ne'
  have hg1C1 : ContDiff ℝ 1 g₁ := hg1C2.of_le (by norm_num)
  have hψ1C1 : ContDiff ℝ 1 (radialFun g₁) := contDiff_radialFun (n := n) hg1C1
  set w : E → ℝ := fun z => v z ^ 2 / radialFun g₁ z with hwdef
  have hwC1 : ContDiff ℝ 1 w := (hv.pow 2).div hψ1C1 hψ1ne
  -- the pointwise Picone inequality
  have hpiconept : ∀ z : E,
      ⟪classicalGrad (radialFun g₁) z, classicalGrad w z⟫_ℝ ≤ ‖classicalGrad v z‖ ^ 2 := by
    intro z
    have hgradw : classicalGrad w z
        = (2 * v z / radialFun g₁ z) • classicalGrad v z
          - (v z ^ 2 / radialFun g₁ z ^ 2) • classicalGrad (radialFun g₁) z :=
      classicalGrad_sq_div (hv.differentiable le_rfl z) (hψ1C1.differentiable le_rfl z)
        (hψ1ne z)
    have hpic := picone_pointwise (v := v z) (hψ1ne z) (classicalGrad v z)
      (classicalGrad (radialFun g₁) z)
    rw [← hgradw] at hpic
    rw [real_inner_comm]
    nlinarith [hpic, sq_nonneg (‖classicalGrad v z
      - (v z / radialFun g₁ z) • classicalGrad (radialFun g₁) z‖)]
  -- integrate
  have hIpair : IntegrableOn
      (fun x : E => ⟪classicalGrad (radialFun g₁) x, classicalGrad w x⟫_ℝ) (ball (0 : E) R) :=
    integrableOn_ball_of_continuous
      ((continuous_classicalGrad (radialFun g₁) hψ1C1).inner
        (continuous_classicalGrad w hwC1)) R
  have hIsq : IntegrableOn (fun x : E => ‖classicalGrad v x‖ ^ 2) (ball (0 : E) R) :=
    (memLp_two_of_continuous (R := R) (continuous_classicalGrad v hv)).norm.integrable_sq
  have hmono : (∫ x in ball (0 : E) R, ⟪classicalGrad (radialFun g₁) x, classicalGrad w x⟫_ℝ)
      ≤ ∫ x in ball (0 : E) R, ‖classicalGrad v x‖ ^ 2 :=
    integral_mono_ae hIpair hIsq (Filter.Eventually.of_forall hpiconept)
  -- rewriting the pieces
  have hpsi1w : ∀ z : E, radialFun g₁ z * w z = v z ^ 2 := by
    intro z
    simp only [hwdef]
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ (hψ1ne z)
  have hg1w_eq : (∫ x in ball (0 : E) R, radialFun g₁ x * w x)
      = ∫ x in ball (0 : E) R, v x ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall hpsi1w)
  have hsphere_w : sphereIntegral n R w = sphereIntegral n R (fun z => v z ^ 2) / g (R ^ 2) := by
    have hpt2 : ∀ y : sphere (0 : E) 1, w (R • (y : E)) = (g (R ^ 2))⁻¹ * v (R • (y : E)) ^ 2 := by
      intro y
      have hnorm : ‖R • (y : E)‖ = R := norm_smul_sphere hR y
      have hψR : radialFun g₁ (R • (y : E)) = g (R ^ 2) := by
        show g₁ (‖R • (y : E)‖ ^ 2) = g (R ^ 2)
        rw [hnorm]; exact heqR2
      simp only [hwdef, hψR, div_eq_inv_mul]
    simp only [sphereIntegral, hpt2, integral_const_mul]
    ring
  have hmass_eq : mass (ofC1 R v hv) = ∫ x in ball (0 : E) R, v x ^ 2 := by
    rw [← integral_norm_toFun_sq (ofC1 R v hv)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [ofC1_toFun, Real.norm_eq_abs, sq_abs]
  have hdirichlet_eq : dirichlet (ofC1 R v hv) = ∫ x in ball (0 : E) R, ‖classicalGrad v x‖ ^ 2 := by
    rw [← integral_norm_grad_sq (ofC1 R v hv), ofC1_grad]
  have hbdReq : bdR n R (ofC1 R v hv) (ofC1 R v hv) = sphereIntegral n R (fun z => v z ^ 2) := by
    rw [bdR_ofC1 hn hR v v hv hv]
    congr 1
    funext z
    ring
  have hmain : (ν * ∫ x in ball (0 : E) R, v x ^ 2)
      + 2 * R * deriv g (R ^ 2) * (sphereIntegral n R (fun z => v z ^ 2) / g (R ^ 2))
      ≤ ∫ x in ball (0 : E) R, ‖classicalGrad v x‖ ^ 2 := by
    calc (ν * ∫ x in ball (0 : E) R, v x ^ 2)
        + 2 * R * deriv g (R ^ 2) * (sphereIntegral n R (fun z => v z ^ 2) / g (R ^ 2))
        = ∫ x in ball (0 : E) R, ⟪classicalGrad (radialFun g₁) x, classicalGrad w x⟫_ℝ := by
          rw [dirichlet_pairing_radial hn hR hg1C2 hg1ode w hwC1, hg1w_eq, hsphere_w, heqR2']
      _ ≤ ∫ x in ball (0 : E) R, ‖classicalGrad v x‖ ^ 2 := hmono
  rw [← hmass_eq, ← hdirichlet_eq, ← hbdReq] at hmain
  have hgR2pos : 0 < g (R ^ 2) := hpos (R ^ 2) (sq_nonneg R) (le_refl _)
  have hbnn : 0 ≤ bdR n R (ofC1 R v hv) (ofC1 R v hv) := bdR_ofC1_self_nonneg hn hR v hv
  have hprod : 0 ≤ (2 * R * deriv g (R ^ 2) + α * g (R ^ 2))
      * bdR n R (ofC1 R v hv) (ofC1 R v hv) := mul_nonneg hrobin hbnn
  have hkey2 : -α * bdR n R (ofC1 R v hv) (ofC1 R v hv)
      ≤ 2 * R * deriv g (R ^ 2)
        * (bdR n R (ofC1 R v hv) (ofC1 R v hv) / g (R ^ 2)) := by
    rw [← mul_div_assoc, le_div_iff₀ hgR2pos]
    nlinarith [hprod]
  linarith [hmain, hkey2]

/-! ## The Picone inequality for all of `H¹` -/

section H1Bound

variable {R : ℝ}

/-- The `H¹`-norm bound for the Dirichlet form on `H1 (ball 0 R)` (Cauchy–Schwarz). -/
theorem abs_dirichletBilin_le' (u w : H1 (ball (0 : E) R)) :
    |dirichletBilin u w| ≤
      Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w) := by
  have hcs := bilin_cauchy_schwarz (N := dirichletBilinₗ (ball (0 : E) R))
    (fun a b => dirichletBilin_comm a b)
    (fun t => by rw [dirichletBilinₗ_apply, dirichletBilin_self]; exact dirichlet_nonneg t) u w
  simp only [dirichletBilinₗ_apply, dirichletBilin_self] at hcs
  rw [← Real.sqrt_mul (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))]
  refine Real.abs_le_sqrt (hcs.trans ?_)
  exact mul_le_mul (le_add_of_nonneg_left (mass_nonneg u))
    (le_add_of_nonneg_left (mass_nonneg w)) (dirichlet_nonneg w)
    (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))

/-- The `H¹`-norm bound for the mass form on `H1 (ball 0 R)` (Cauchy–Schwarz). -/
theorem abs_massBilin_le' (u w : H1 (ball (0 : E) R)) :
    |massBilin u w| ≤
      Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w) := by
  have hcs := bilin_cauchy_schwarz (N := massBilinₗ (ball (0 : E) R))
    (fun a b => massBilin_comm a b)
    (fun t => by rw [massBilinₗ_apply, massBilin_self]; exact mass_nonneg t) u w
  simp only [massBilinₗ_apply, massBilin_self] at hcs
  rw [← Real.sqrt_mul (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))]
  refine Real.abs_le_sqrt (hcs.trans ?_)
  exact mul_le_mul (le_add_of_nonneg_right (dirichlet_nonneg u))
    (le_add_of_nonneg_right (dirichlet_nonneg w)) (mass_nonneg w)
    (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))

end H1Bound

/-- **Picone inequality for all of `H¹`** (by density of `C¹` functions). -/
theorem picone_H1 (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {α : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) {ν : ℝ}
    (hode : ∀ s, 0 ≤ s → s < R ^ 2 → 4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s
      + ν * g s = 0)
    (hpos : ∀ s, 0 ≤ s → s ≤ R ^ 2 → 0 < g s)
    (hrobin : 0 ≤ 2 * R * deriv g (R ^ 2) + α * g (R ^ 2))
    (v : H1 (ball (0 : E) R)) :
    ν * mass v ≤ dirichlet v + α * bdR n R v v := by
  -- the bounded symmetric bilinear form whose diagonal is the quantity of interest
  set F : H1 (ball (0 : E) R) →ₗ[ℝ] H1 (ball (0 : E) R) →ₗ[ℝ] ℝ :=
    dirichletBilinₗ (ball (0 : E) R) + α • bdR n R - ν • massBilinₗ (ball (0 : E) R) with hFdef
  have hFapply : ∀ u w : H1 (ball (0 : E) R),
      F u w = dirichletBilin u w + α * bdR n R u w - ν * massBilin u w := by
    intro u w
    simp only [hFdef, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, dirichletBilinₗ_apply, massBilinₗ_apply]
  have hFself : ∀ u : H1 (ball (0 : E) R), F u u = dirichlet u + α * bdR n R u u - ν * mass u := by
    intro u
    rw [hFapply, dirichletBilin_self, massBilin_self]
  have hFsymm : ∀ u w : H1 (ball (0 : E) R), F u w = F w u := by
    intro u w
    rw [hFapply, hFapply, dirichletBilin_comm, bdR_symm, massBilin_comm]
  have hFbound : ∀ u w : H1 (ball (0 : E) R), |F u w| ≤
      (1 + α * ((n : ℝ) / R + 1) + |ν|) *
        Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w) := by
    intro u w
    rw [hFapply]
    have h1 := abs_dirichletBilin_le' u w
    have h2 := abs_bdR_le₂ hR u w
    have h3 := abs_massBilin_le' u w
    have hstep : |dirichletBilin u w + α * bdR n R u w - ν * massBilin u w|
        ≤ |dirichletBilin u w| + |α * bdR n R u w| + |ν * massBilin u w| := by
      have e1 := abs_add_le (dirichletBilin u w + α * bdR n R u w) (-(ν * massBilin u w))
      have e2 := abs_add_le (dirichletBilin u w) (α * bdR n R u w)
      rw [abs_neg] at e1
      have heq : dirichletBilin u w + α * bdR n R u w - ν * massBilin u w
          = dirichletBilin u w + α * bdR n R u w + (-(ν * massBilin u w)) := by ring
      rw [heq]
      linarith [e1, e2]
    have h2' : |α * bdR n R u w| ≤
        α * ((n : ℝ) / R + 1) * (Real.sqrt (mass u + dirichlet u)
          * Real.sqrt (mass w + dirichlet w)) := by
      rw [abs_mul, abs_of_nonneg hα]
      calc α * |bdR n R u w| ≤ α * (((n : ℝ) / R + 1)
              * (Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w))) := by
            apply mul_le_mul_of_nonneg_left _ hα
            calc |bdR n R u w| ≤ ((n : ℝ) / R + 1) * Real.sqrt (mass u + dirichlet u)
                  * Real.sqrt (mass w + dirichlet w) := h2
              _ = ((n : ℝ) / R + 1) * (Real.sqrt (mass u + dirichlet u)
                    * Real.sqrt (mass w + dirichlet w)) := by ring
        _ = α * ((n : ℝ) / R + 1) * (Real.sqrt (mass u + dirichlet u)
              * Real.sqrt (mass w + dirichlet w)) := by ring
    have h3' : |ν * massBilin u w| ≤
        |ν| * (Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h3 (abs_nonneg ν)
    calc |dirichletBilin u w + α * bdR n R u w - ν * massBilin u w|
        ≤ |dirichletBilin u w| + |α * bdR n R u w| + |ν * massBilin u w| := hstep
      _ ≤ Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w)
          + α * ((n : ℝ) / R + 1) * (Real.sqrt (mass u + dirichlet u)
            * Real.sqrt (mass w + dirichlet w))
          + |ν| * (Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w)) := by
          gcongr
      _ = (1 + α * ((n : ℝ) / R + 1) + |ν|) *
            Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass w + dirichlet w) := by ring
  -- it suffices to bound `F v v` below by `0`
  have hgoal : 0 ≤ F v v := by
    set C : ℝ := 1 + α * ((n : ℝ) / R + 1) + |ν| with hCdef
    have hC : 0 ≤ C := by positivity
    set K : ℝ := mass v + dirichlet v with hKdef
    have hK : 0 ≤ K := add_nonneg (mass_nonneg v) (dirichlet_nonneg v)
    set M : ℝ := C * (1 + 2 * Real.sqrt K) + 1 with hMdef
    have hM1 : 1 ≤ M := by
      have : 0 ≤ C * (1 + 2 * Real.sqrt K) := mul_nonneg hC (by positivity)
      linarith
    have hM : 0 < M := by linarith
    have he : ∀ t : H1 (ball (0 : E) R), 0 ≤ mass t + dirichlet t :=
      fun t => add_nonneg (mass_nonneg t) (dirichlet_nonneg t)
    have hcont := abs_bilin_self_sub_le (F := F) hFsymm he (C := C) hFbound
    refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
    set δ : ℝ := -a with hδdef
    have hδ : 0 < δ := by linarith
    set η : ℝ := min 1 ((δ / M) ^ 2) with hηdef
    have hη : 0 < η := lt_min one_pos (by positivity)
    obtain ⟨v1, hv1, hclose⟩ := exists_ofC1_h1_close hR v hη
    set w1 : H1 (ball (0 : E) R) := ofC1 R v1 hv1 with hw1def
    set e : ℝ := mass (w1 - v) + dirichlet (w1 - v) with hedef
    have he0 : 0 ≤ e := he _
    have heη : e ≤ η := hclose
    have hw0 : 0 ≤ F w1 w1 := by
      rw [hFself]
      have := picone_ofC1 hn hR hα hg hode hpos hrobin v1 hv1
      linarith
    have hdiff := hcont w1 v
    simp only at hdiff
    set s : ℝ := Real.sqrt e with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg e
    have hss : s * s = e := Real.mul_self_sqrt he0
    have hs1 : s ≤ 1 := by
      rw [hsdef, Real.sqrt_le_one]
      exact heη.trans (min_le_left _ _)
    have hsδ : s ≤ δ / M := by
      rw [hsdef]
      calc Real.sqrt e ≤ Real.sqrt ((δ / M) ^ 2) :=
            Real.sqrt_le_sqrt (heη.trans (min_le_right _ _))
        _ = δ / M := Real.sqrt_sq (by positivity)
    have hes : e ≤ s := by nlinarith
    have hbound : C * (e + 2 * s * Real.sqrt K) ≤ δ := by
      have hsqK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
      have h1 : C * (e + 2 * s * Real.sqrt K) ≤ s * (C * (1 + 2 * Real.sqrt K)) := by
        have hstep2 : C * (e + 2 * s * Real.sqrt K) ≤ C * (s + 2 * s * Real.sqrt K) := by
          gcongr
        linarith [hstep2]
      have h2 : s * (C * (1 + 2 * Real.sqrt K)) ≤ δ / M * (M - 1) := by
        have hpos' : 0 ≤ C * (1 + 2 * Real.sqrt K) := mul_nonneg hC (by positivity)
        calc s * (C * (1 + 2 * Real.sqrt K)) ≤ δ / M * (C * (1 + 2 * Real.sqrt K)) := by gcongr
          _ = δ / M * (M - 1) := by rw [hMdef]; ring
      have h3 : δ / M * (M - 1) ≤ δ := by
        have heqδ : δ / M * (M - 1) = δ - δ / M := by field_simp
        rw [heqδ]
        have : 0 ≤ δ / M := by positivity
        linarith
      linarith
    have habs := abs_le.mp hdiff
    rw [hδdef] at hbound
    linarith [habs.1, habs.2, hw0]
  rw [hFself] at hgoal
  linarith [hgoal]

end RobinCaps.Compact

end
