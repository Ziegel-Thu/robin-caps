import RobinCaps.Compact.Basic
import RobinCaps.Compact.Contraction
import RobinCaps.Compact.SmoothEstimates
import RobinCaps.Compact.WeakGradMollify
import RobinCaps.Compact.Dilation
import RobinCaps.Compact.L2Approx

/-!
# Smooth approximation of `H¹(B_R)`: the estimates (A1) and (A2)

This file assembles the approximation step of the Rellich–Kondrachov argument of
`RobinCaps/Compact/PLAN.md`.  For `u ∈ H¹(B_R)`, `1/2 ≤ λ < 1` and `0 < ε` with `R + ε < R/λ`,
the **smooth approximant** is

  `approx u λ ε := ρ_ε ⋆ ext (D_λ u)`,

the mollification (at scale `ε`) of the zero-extension of the dilation `D_λ u ∈ H¹(B_{R/λ})`.
It is a smooth function on all of `ℝⁿ`.  We prove:

* **(S-weak)** `integral_ball_conv_ext_sub_sq_le`: for `w ∈ H¹(B_{R'})` and `R + ε < R'`,
  `∫_{B_R} (ρ_ε ⋆ w̄ − w̄)² ≤ ε² ∫_{B_{R'}} |∇w|²`.  Proof: apply the smooth estimate (S-smooth)
  of `SmoothEstimates.lean` to the `C¹` function `v = ρ_δ ⋆ w̄`, bound `∫_{B_{R+ε}} |∇v|²` by the
  Dirichlet energy of `w` through (WG) (`WeakGradMollify.lean`) and the contraction (J)
  (`Contraction.lean`), and let `δ → 0` using (M) (`L2Approx.lean`) and Minkowski's inequality.
* **(D-weak)** `integral_ball_ext_dilate_sub_sq_le`:
  `∫_{B_R} (ū(λ·) − ū)² ≤ (1−λ)² R² 2ⁿ ∫_{B_R} |∇u|²`.  Proof: the same scheme on `B_r`, `r < R`,
  with (D-smooth) in place of (S-smooth), followed by monotone convergence `r ↑ R`.
* **(A1)** `integral_ball_approx_sub_sq_le`:
  `∫_{B_R} (approx u λ ε − u)² ≤ 2^{n+1} (ε + (1−λ) R)² ∫_{B_R} |∇u|²`.
* **(A2)** `exists_approx_grad_close`: `∇ (approx u λ ε) → ∇u` in `L²(B_R)` as `λ → 1⁻` and
  then `ε → 0⁺`.  Proof: on `B_R` the gradient of the approximant is the vector of the
  mollified components of the weak gradient of `D_λ u` (by (WG)); the pointwise inequality
  `(p + q + r)² ≤ 3 (p² + q² + r²)` reduces the claim to (M) and (M') for the finitely many
  components of `∇u`.

Convolutions are scalar convolutions with respect to Lebesgue measure:
`ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## `L²` tools for a general measure -/

section L2Tools

variable {μ : Measure (EuclideanSpace ℝ (Fin n))}

/-- The squared `L²(μ)` distance of two `Lp` classes is the integral of the squared difference
of representatives. -/
theorem dist_toLp_sq_measure {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg)] with x hx
  rw [hx]
  simp [Pi.sub_apply, pow_two]

/-- `√(∫ (f - g)² ∂μ)` is the `L²(μ)` distance of the classes of `f` and `g`. -/
theorem sqrt_integral_sub_sq_eq_dist_measure {f g : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, (f x - g x) ^ 2 ∂μ) = dist (hf.toLp f) (hg.toLp g) := by
  rw [← dist_toLp_sq_measure hf hg, Real.sqrt_sq dist_nonneg]

/-- **Minkowski's inequality** for a general measure (in particular for `volume.restrict s`). -/
theorem sqrt_integral_sub_sq_le_add_measure {f g h : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    Real.sqrt (∫ x, (f x - h x) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ x, (f x - g x) ^ 2 ∂μ) + Real.sqrt (∫ x, (g x - h x) ^ 2 ∂μ) := by
  rw [sqrt_integral_sub_sq_eq_dist_measure hf hh, sqrt_integral_sub_sq_eq_dist_measure hf hg,
    sqrt_integral_sub_sq_eq_dist_measure hg hh]
  exact dist_triangle _ _ _

/-- The squared difference of two `L²` functions is integrable. -/
theorem integrable_sub_sq {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => (f x - g x) ^ 2) μ :=
  (hf.sub hg).integrable_sq

end L2Tools

/-- A set integral of a squared difference is bounded by the integral over all of `ℝⁿ`. -/
theorem setIntegral_sub_sq_le_integral {f g : E → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (s : Set E) :
    ∫ x in s, (f x - g x) ^ 2 ≤ ∫ x, (f x - g x) ^ 2 :=
  setIntegral_le_integral (integrable_sub_sq hf hg) (Eventually.of_forall fun _ => sq_nonneg _)

theorem setIntegral_sub_sq_nonneg (f g : E → ℝ) (s : Set E) :
    0 ≤ ∫ x in s, (f x - g x) ^ 2 :=
  integral_nonneg fun _ => sq_nonneg _

/-- If `a ≤ b + K √η` for every `η > 0`, then `a ≤ b`. -/
theorem le_of_forall_le_add_mul_sqrt {a b K : ℝ} (hK : 0 ≤ K)
    (h : ∀ η : ℝ, 0 < η → a ≤ b + K * Real.sqrt η) : a ≤ b := by
  refine le_of_forall_pos_le_add fun θ hθ => ?_
  have hK1 : 0 < K + 1 := by linarith
  have hη : 0 < (θ / (K + 1)) ^ 2 := by positivity
  calc a ≤ b + K * Real.sqrt ((θ / (K + 1)) ^ 2) := h _ hη
    _ = b + K * (θ / (K + 1)) := by rw [Real.sqrt_sq (by positivity)]
    _ ≤ b + θ := by
        have : K * (θ / (K + 1)) ≤ θ := by
          rw [mul_div_assoc', div_le_iff₀ hK1]
          nlinarith
        linarith

/-- For `1/2 ≤ lam`, `lam⁻¹ ^ n ≤ 2 ^ n`. -/
theorem inv_pow_le_two_pow {lam : ℝ} (hlam : 1 / 2 ≤ lam) : lam⁻¹ ^ n ≤ 2 ^ n := by
  have hlam0 : 0 < lam := by linarith
  have h : lam⁻¹ ≤ 2 := inv_le_of_inv_le₀ two_pos (by rwa [one_div] at hlam)
  exact pow_le_pow_left₀ (inv_nonneg.2 hlam0.le) h n

/-! ## The gradient of a mollified extension -/

section Grad

variable {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Gradient bound for a mollified extension.**  For `w ∈ H¹(B_{R'})` and `r + δ ≤ R'`,
`∫_{B_r} ‖∇(ρ_δ ⋆ w̄)‖² ≤ ∫_{B_{R'}} |∇w|²`: by (WG) the integrand is `∑ᵢ (ρ_δ ⋆ extGrad w i)²`
on `B_r`, and each term is contracted by (J). -/
theorem integral_ball_norm_fderiv_conv_ext_le (hρ : IsMollifier δ ρ) {R' : ℝ}
    (w : H1 (ball (0 : E) R')) {r : ℝ} (hr : r + δ ≤ R') :
    ∫ x in ball (0 : E) r, ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x‖ ^ 2
      ≤ dirichlet w := by
  have hint : ∀ i, Integrable
      (fun x => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x) ^ 2) :=
    fun i => (memLp_conv hρ (memLp_extGrad w i)).integrable_sq
  calc ∫ x in ball (0 : E) r, ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x‖ ^ 2
      = ∫ x in ball (0 : E) r,
          ∑ i, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
        rw [mem_ball, dist_zero_right] at hx
        exact norm_fderiv_conv_ext_eq hρ w (by linarith)
    _ = ∑ i, ∫ x in ball (0 : E) r,
          ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x) ^ 2 :=
        integral_finset_sum _ fun i _ => (hint i).integrableOn
    _ ≤ ∑ i, ∫ x, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          setIntegral_le_integral (hint i) (Eventually.of_forall fun _ => sq_nonneg _)
    _ ≤ ∑ i, ∫ x, extGrad w i x ^ 2 :=
        Finset.sum_le_sum fun i _ => integral_conv_sq_le hρ (memLp_extGrad w i)
    _ = dirichlet w := sum_integral_extGrad_sq w

end Grad

/-- The mollified extension is `C¹`. -/
theorem contDiff_one_conv_ext {δ : ℝ} (hδ : 0 < δ) {R' : ℝ} (w : H1 (ball (0 : E) R')) :
    ContDiff ℝ 1 (mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) :=
  ((isMollifier_mollifier hδ).contDiff_conv (locallyIntegrable_ext w)).of_le (by simp)

/-! ## (S-weak): the mollification error -/

/-- **(S-weak): mollification error on `B_R` for `w ∈ H¹(B_{R'})`, `R + ε < R'`.** -/
theorem integral_ball_conv_ext_sub_sq_le {R' : ℝ} (w : H1 (ball (0 : E) R')) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hR' : R + ε < R') :
    ∫ x in ball (0 : E) R,
        ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext w x) ^ 2
      ≤ ε ^ 2 * dirichlet w := by
  have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
  have hw : MemLp (ext w) 2 volume := memLp_ext w
  have hD : 0 ≤ dirichlet w := dirichlet_nonneg w
  have hρw : MemLp (mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) 2 volume :=
    memLp_conv hρ hw
  have hA0 : 0 ≤ ∫ x in ball (0 : E) R,
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext w x) ^ 2 :=
    setIntegral_sub_sq_nonneg _ _ _
  -- the key estimate: `√A ≤ ε √(dirichlet w) + 2 √η` for every `η > 0`
  have key : ∀ η : ℝ, 0 < η →
      Real.sqrt (∫ x in ball (0 : E) R,
        ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext w x) ^ 2)
        ≤ ε * Real.sqrt (dirichlet w) + 2 * Real.sqrt η := by
    intro η hη
    obtain ⟨δ₀, hδ₀, hδ⟩ := exists_delta_conv_close hw hη
    set δ : ℝ := min (δ₀ / 2) ((R' - R - ε) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ1 : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ2 : R + ε + δ ≤ R' := by
      have := min_le_right (δ₀ / 2) ((R' - R - ε) / 2)
      linarith
    have hρδ : IsMollifier δ (mollifier (n := n) δ) := isMollifier_mollifier hδpos
    set v : E → ℝ := mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w with hvdef
    have hv : ContDiff ℝ 1 v := contDiff_one_conv_ext hδpos w
    have hv2 : MemLp v 2 volume := memLp_conv hρδ hw
    have hvw : ∫ x, (v x - ext w x) ^ 2 ≤ η := hδ δ hδpos hδ1
    have hwv : ∫ x, (ext w x - v x) ^ 2 ≤ η := by
      rw [integral_sub_sq_comm]
      exact hvw
    have hρv : MemLp (mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) 2 volume :=
      memLp_conv hρ hv2
    -- the three terms of the triangle inequality
    have hT1 : ∫ x in ball (0 : E) R,
        ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x
          - (mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x) ^ 2 ≤ η :=
      (setIntegral_sub_sq_le_integral hρw hρv _).trans
        ((integral_conv_sub_sq_le hρ hw hv2).trans hwv)
    have hT2 : ∫ x in ball (0 : E) R,
        ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2
          ≤ ε ^ 2 * dirichlet w :=
      (integral_ball_conv_sub_sq_le hρ hε.le hv hR).trans
        (mul_le_mul_of_nonneg_left (integral_ball_norm_fderiv_conv_ext_le hρδ w hδ2)
          (sq_nonneg ε))
    have hT3 : ∫ x in ball (0 : E) R, (v x - ext w x) ^ 2 ≤ η :=
      (setIntegral_sub_sq_le_integral hv2 hw _).trans hvw
    calc Real.sqrt (∫ x in ball (0 : E) R,
          ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext w x) ^ 2)
        ≤ Real.sqrt (∫ x in ball (0 : E) R,
            ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x
              - (mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x) ^ 2)
          + Real.sqrt (∫ x in ball (0 : E) R,
            ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - ext w x) ^ 2) :=
          sqrt_integral_sub_sq_le_add_measure (hρw.restrict _) (hρv.restrict _) (hw.restrict _)
      _ ≤ Real.sqrt (∫ x in ball (0 : E) R,
            ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x
              - (mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x) ^ 2)
          + (Real.sqrt (∫ x in ball (0 : E) R,
              ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
            + Real.sqrt (∫ x in ball (0 : E) R, (v x - ext w x) ^ 2)) :=
          add_le_add le_rfl
            (sqrt_integral_sub_sq_le_add_measure (hρv.restrict _) (hv2.restrict _)
              (hw.restrict _))
      _ ≤ Real.sqrt η + (Real.sqrt (ε ^ 2 * dirichlet w) + Real.sqrt η) :=
          add_le_add (Real.sqrt_le_sqrt hT1)
            (add_le_add (Real.sqrt_le_sqrt hT2) (Real.sqrt_le_sqrt hT3))
      _ = ε * Real.sqrt (dirichlet w) + 2 * Real.sqrt η := by
          rw [Real.sqrt_mul' _ hD, Real.sqrt_sq hε.le]
          ring
  have hsqrt := le_of_forall_le_add_mul_sqrt (by norm_num) key
  refine le_of_sqrt_le_sqrt hA0 (by positivity) ?_
  rw [Real.sqrt_mul' _ hD, Real.sqrt_sq hε.le]
  exact hsqrt

/-! ## (D-weak): the dilation error -/

/-- **(D-weak) on a smaller ball `B_r`, `r < R`.** -/
theorem integral_ball_ext_dilate_sub_sq_le_of_lt {R : ℝ} (hR : 0 < R)
    (u : H1 (ball (0 : E) R)) {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ∫ x in ball (0 : E) r, (ext u (lam • x) - ext u x) ^ 2
      ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := by
  have hlam0 : 0 < lam := by linarith
  have hu : MemLp (ext u) 2 volume := memLp_ext u
  have hD : 0 ≤ dirichlet u := dirichlet_nonneg u
  have hC0 : 0 ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := by positivity
  have hA0 : 0 ≤ ∫ x in ball (0 : E) r, (ext u (lam • x) - ext u x) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h2n : lam⁻¹ ^ n ≤ 2 ^ n := inv_pow_le_two_pow hlam
  have hulam : MemLp (fun x => ext u (lam • x)) 2 volume := memLp_comp_smul hu hlam0
  have key : ∀ η : ℝ, 0 < η →
      Real.sqrt (∫ x in ball (0 : E) r, (ext u (lam • x) - ext u x) ^ 2)
        ≤ Real.sqrt ((1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u)
          + (Real.sqrt (2 ^ n) + 1) * Real.sqrt η := by
    intro η hη
    obtain ⟨δ₀, hδ₀, hδ⟩ := exists_delta_conv_close hu hη
    set δ : ℝ := min (δ₀ / 2) ((R - r) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ1 : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ2 : r + δ ≤ R := by
      have := min_le_right (δ₀ / 2) ((R - r) / 2)
      linarith
    have hρδ : IsMollifier δ (mollifier (n := n) δ) := isMollifier_mollifier hδpos
    set v : E → ℝ := mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext u with hvdef
    have hv : ContDiff ℝ 1 v := contDiff_one_conv_ext hδpos u
    have hv2 : MemLp v 2 volume := memLp_conv hρδ hu
    have hvu : ∫ x, (v x - ext u x) ^ 2 ≤ η := hδ δ hδpos hδ1
    have huv : ∫ x, (ext u x - v x) ^ 2 ≤ η := by
      rw [integral_sub_sq_comm]
      exact hvu
    have hvlam : MemLp (fun x => v (lam • x)) 2 volume := memLp_comp_smul hv2 hlam0
    -- the three terms of the triangle inequality
    have hT1 : ∫ x in ball (0 : E) r, (ext u (lam • x) - v (lam • x)) ^ 2 ≤ 2 ^ n * η := by
      have h := integral_ball_comp_smul_sq (fun y => ext u y - v y) hlam0 r
      beta_reduce at h
      rw [h]
      have h' : ∫ x in ball (0 : E) (lam * r), (ext u x - v x) ^ 2 ≤ η :=
        (setIntegral_sub_sq_le_integral hu hv2 _).trans huv
      exact mul_le_mul h2n h' (setIntegral_sub_sq_nonneg _ _ _) (by positivity)
    have hT2 : ∫ x in ball (0 : E) r, (v (lam • x) - v x) ^ 2
        ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := by
      calc ∫ x in ball (0 : E) r, (v (lam • x) - v x) ^ 2
          ≤ (1 - lam) ^ 2 * r ^ 2 * 2 ^ n * ∫ x in ball (0 : E) r, ‖fderiv ℝ v x‖ ^ 2 :=
            integral_ball_dilate_sub_sq_le hv hr hlam hlam1
        _ ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := by
            have hgrad := integral_ball_norm_fderiv_conv_ext_le hρδ u hδ2
            have hr2 : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hrR.le 2
            have hI0 : 0 ≤ ∫ x in ball (0 : E) r, ‖fderiv ℝ v x‖ ^ 2 :=
              integral_nonneg fun _ => sq_nonneg _
            calc (1 - lam) ^ 2 * r ^ 2 * 2 ^ n * ∫ x in ball (0 : E) r, ‖fderiv ℝ v x‖ ^ 2
                ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * ∫ x in ball (0 : E) r, ‖fderiv ℝ v x‖ ^ 2 := by
                  gcongr
              _ ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := by gcongr
    have hT3 : ∫ x in ball (0 : E) r, (v x - ext u x) ^ 2 ≤ η :=
      (setIntegral_sub_sq_le_integral hv2 hu _).trans hvu
    calc Real.sqrt (∫ x in ball (0 : E) r, (ext u (lam • x) - ext u x) ^ 2)
        ≤ Real.sqrt (∫ x in ball (0 : E) r, (ext u (lam • x) - v (lam • x)) ^ 2)
          + Real.sqrt (∫ x in ball (0 : E) r, (v (lam • x) - ext u x) ^ 2) :=
          sqrt_integral_sub_sq_le_add_measure (hulam.restrict _) (hvlam.restrict _)
            (hu.restrict _)
      _ ≤ Real.sqrt (∫ x in ball (0 : E) r, (ext u (lam • x) - v (lam • x)) ^ 2)
          + (Real.sqrt (∫ x in ball (0 : E) r, (v (lam • x) - v x) ^ 2)
            + Real.sqrt (∫ x in ball (0 : E) r, (v x - ext u x) ^ 2)) :=
          add_le_add le_rfl
            (sqrt_integral_sub_sq_le_add_measure (hvlam.restrict _) (hv2.restrict _)
              (hu.restrict _))
      _ ≤ Real.sqrt (2 ^ n * η)
          + (Real.sqrt ((1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u) + Real.sqrt η) :=
          add_le_add (Real.sqrt_le_sqrt hT1)
            (add_le_add (Real.sqrt_le_sqrt hT2) (Real.sqrt_le_sqrt hT3))
      _ = Real.sqrt ((1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u)
          + (Real.sqrt (2 ^ n) + 1) * Real.sqrt η := by
          rw [Real.sqrt_mul (by positivity) η]
          ring
  have hsqrt := le_of_forall_le_add_mul_sqrt (by positivity) key
  exact le_of_sqrt_le_sqrt hA0 hC0 hsqrt

/-- **(D-weak): dilation error on `B_R`.** -/
theorem integral_ball_ext_dilate_sub_sq_le {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R))
    {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) :
    ∫ x in ball (0 : E) R, (ext u (lam • x) - ext u x) ^ 2
      ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := by
  have hlam0 : 0 < lam := by linarith
  have hFi : Integrable (fun x => (ext u (lam • x) - ext u x) ^ 2) :=
    integrable_sub_sq (memLp_comp_smul (memLp_ext u) hlam0) (memLp_ext u)
  -- the exhausting radii `r k = R - R / (k + 1)`
  set r : ℕ → ℝ := fun k => R - R / ((k : ℝ) + 1) with hr
  have hr0 : ∀ k, 0 ≤ r k := fun k => by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : R / ((k : ℝ) + 1) ≤ R := div_le_self hR.le (by linarith)
    simp only [hr]
    linarith
  have hrR : ∀ k, r k < R := fun k => by
    have : 0 < R / ((k : ℝ) + 1) := by positivity
    simp only [hr]
    linarith
  have hmono : Monotone fun k => ball (0 : E) (r k) := by
    intro k l hkl
    apply ball_subset_ball
    have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by
      have : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
      linarith
    have : R / ((l : ℝ) + 1) ≤ R / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_left hR.le (by positivity) hkl'
    simp only [hr]
    linarith
  have hunion : (⋃ k, ball (0 : E) (r k)) = ball (0 : E) R := by
    apply Subset.antisymm
    · exact iUnion_subset fun k => ball_subset_ball (hrR k).le
    · intro x hx
      rw [mem_ball, dist_zero_right] at hx
      have ht : 0 < R - ‖x‖ := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (R / (R - ‖x‖))
      have hk' : R < (R - ‖x‖) * ((k : ℝ) + 1) := by
        have h1 : R < (k : ℝ) * (R - ‖x‖) := (div_lt_iff₀ ht).1 hk
        nlinarith
      have hk'' : R / ((k : ℝ) + 1) < R - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        linarith
      refine mem_iUnion.2 ⟨k, ?_⟩
      rw [mem_ball, dist_zero_right]
      simp only [hr]
      linarith
  have hT : Tendsto (fun k => ∫ x in ball (0 : E) (r k), (ext u (lam • x) - ext u x) ^ 2)
      atTop (𝓝 (∫ x in ball (0 : E) R, (ext u (lam • x) - ext u x) ^ 2)) := by
    have := tendsto_setIntegral_of_monotone (fun k => measurableSet_ball) hmono
      (hFi.integrableOn (s := ⋃ k, ball (0 : E) (r k)))
    rwa [hunion] at this
  exact le_of_tendsto' hT fun k =>
    integral_ball_ext_dilate_sub_sq_le_of_lt hR u hlam hlam1 (hr0 k) (hrR k)

/-! ## The smooth approximant -/

/-- **The smooth approximant** `S_ε D_lam u = ρ_ε ⋆ ext (D_lam u)`. -/
def approx {R : ℝ} (u : H1 (ball (0 : E) R)) (lam ε : ℝ) (hlam : 0 < lam) : E → ℝ :=
  mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext (dilate lam hlam u)

theorem approx_def {R : ℝ} (u : H1 (ball (0 : E) R)) (lam ε : ℝ) (hlam : 0 < lam) :
    approx u lam ε hlam
      = mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext (dilate lam hlam u) := rfl

/-- The approximant is smooth. -/
theorem contDiff_approx {R : ℝ} (u : H1 (ball (0 : E) R)) {lam ε : ℝ} (hlam : 0 < lam)
    (hε : 0 < ε) : ContDiff ℝ ∞ (approx u lam ε hlam) :=
  (isMollifier_mollifier hε).contDiff_conv (locallyIntegrable_ext _)

/-- The approximant is continuous. -/
theorem continuous_approx {R : ℝ} (u : H1 (ball (0 : E) R)) {lam ε : ℝ} (hlam : 0 < lam)
    (hε : 0 < ε) : Continuous (approx u lam ε hlam) :=
  (contDiff_approx u hlam hε).continuous

/-- The Dirichlet energy of the dilation, for `1/2 ≤ lam ≤ 1`. -/
theorem dirichlet_dilate_le {R : ℝ} (u : H1 (ball (0 : E) R)) {lam : ℝ} (hlam : 1 / 2 ≤ lam)
    (hlam1 : lam ≤ 1) (hlam0 : 0 < lam) :
    dirichlet (dilate lam hlam0 u) ≤ 2 ^ n * dirichlet u := by
  rw [dirichlet_dilate]
  have hD : 0 ≤ dirichlet u := dirichlet_nonneg u
  have h1 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam0.le hlam1
  have h2 : lam⁻¹ ^ n ≤ 2 ^ n := inv_pow_le_two_pow hlam
  calc lam ^ 2 * lam⁻¹ ^ n * dirichlet u ≤ 1 * 2 ^ n * dirichlet u := by gcongr
    _ = 2 ^ n * dirichlet u := by ring

/-! ## (A1): `L²` convergence of the approximant -/

/-- **(A1), sharp form.**
`∫_{B_R} (approx u lam ε − u)² ≤ 2ⁿ (ε + (1 − lam) R)² dirichlet u`. -/
theorem integral_ball_approx_sub_sq_le' {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R))
    {lam ε : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1) (hε : 0 < ε) (hε' : R + ε < R / lam)
    (hlam0 : 0 < lam) :
    ∫ x in ball (0 : E) R, (approx u lam ε hlam0 x - u.toFun x) ^ 2
      ≤ 2 ^ n * (ε + (1 - lam) * R) ^ 2 * dirichlet u := by
  have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
  set w := dilate lam hlam0 u with hw
  have hD : 0 ≤ dirichlet u := dirichlet_nonneg u
  have hDw : dirichlet w ≤ 2 ^ n * dirichlet u := dirichlet_dilate_le u hlam hlam1.le hlam0
  have hM0 : 0 ≤ 2 ^ n * dirichlet u := by positivity
  have hlamR : 0 ≤ (1 - lam) * R := mul_nonneg (by linarith) hR.le
  -- replace `u.toFun` by `ext u` on the ball
  have hLHS : ∫ x in ball (0 : E) R, (approx u lam ε hlam0 x - u.toFun x) ^ 2
      = ∫ x in ball (0 : E) R,
          ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext u x) ^ 2 :=
    setIntegral_congr_fun measurableSet_ball fun x hx => by rw [ext_apply_of_mem u hx]; rfl
  rw [hLHS]
  have hA0 : 0 ≤ ∫ x in ball (0 : E) R,
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext u x) ^ 2 :=
    setIntegral_sub_sq_nonneg _ _ _
  -- the two error terms
  have hT1 : ∫ x in ball (0 : E) R,
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext w x) ^ 2
        ≤ ε ^ 2 * (2 ^ n * dirichlet u) :=
    (integral_ball_conv_ext_sub_sq_le w hR.le hε hε').trans
      (mul_le_mul_of_nonneg_left hDw (sq_nonneg _))
  have hT2 : ∫ x in ball (0 : E) R, (ext w x - ext u x) ^ 2
      ≤ ((1 - lam) * R) ^ 2 * (2 ^ n * dirichlet u) := by
    have h := integral_ball_ext_dilate_sub_sq_le hR u hlam hlam1.le
    simp only [hw, ext_dilate]
    calc ∫ x in ball (0 : E) R, (ext u (lam • x) - ext u x) ^ 2
        ≤ (1 - lam) ^ 2 * R ^ 2 * 2 ^ n * dirichlet u := h
      _ = ((1 - lam) * R) ^ 2 * (2 ^ n * dirichlet u) := by ring
  have hsqrt : Real.sqrt (∫ x in ball (0 : E) R,
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext u x) ^ 2)
        ≤ (ε + (1 - lam) * R) * Real.sqrt (2 ^ n * dirichlet u) := by
    calc Real.sqrt (∫ x in ball (0 : E) R,
          ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext u x) ^ 2)
        ≤ Real.sqrt (∫ x in ball (0 : E) R,
            ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext w x) ^ 2)
          + Real.sqrt (∫ x in ball (0 : E) R, (ext w x - ext u x) ^ 2) :=
          sqrt_integral_sub_sq_le_add_measure ((memLp_conv hρ (memLp_ext w)).restrict _)
            ((memLp_ext w).restrict _) ((memLp_ext u).restrict _)
      _ ≤ Real.sqrt (ε ^ 2 * (2 ^ n * dirichlet u))
          + Real.sqrt (((1 - lam) * R) ^ 2 * (2 ^ n * dirichlet u)) :=
          add_le_add (Real.sqrt_le_sqrt hT1) (Real.sqrt_le_sqrt hT2)
      _ = (ε + (1 - lam) * R) * Real.sqrt (2 ^ n * dirichlet u) := by
          rw [Real.sqrt_mul' _ hM0, Real.sqrt_sq hε.le, Real.sqrt_mul' _ hM0,
            Real.sqrt_sq hlamR]
          ring
  calc ∫ x in ball (0 : E) R,
        ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext u x) ^ 2
      = Real.sqrt (∫ x in ball (0 : E) R,
          ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ext w) x - ext u x) ^ 2) ^ 2 :=
        (Real.sq_sqrt hA0).symm
    _ ≤ ((ε + (1 - lam) * R) * Real.sqrt (2 ^ n * dirichlet u)) ^ 2 := by
        gcongr
    _ = 2 ^ n * (ε + (1 - lam) * R) ^ 2 * dirichlet u := by
        rw [mul_pow, Real.sq_sqrt hM0]
        ring

/-- **(A1).**  `∫_{B_R} (approx u lam ε − u)² ≤ 2^{n+1} (ε + (1 − lam) R)² dirichlet u`. -/
theorem integral_ball_approx_sub_sq_le {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R))
    {lam ε : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam < 1) (hε : 0 < ε) (hε' : R + ε < R / lam) :
    ∫ x in ball (0 : E) R, (approx u lam ε (by linarith) x - u.toFun x) ^ 2
      ≤ 2 ^ (n + 1) * (ε + (1 - lam) * R) ^ 2 * dirichlet u := by
  have hD : 0 ≤ dirichlet u := dirichlet_nonneg u
  calc ∫ x in ball (0 : E) R, (approx u lam ε (by linarith) x - u.toFun x) ^ 2
      ≤ 2 ^ n * (ε + (1 - lam) * R) ^ 2 * dirichlet u :=
        integral_ball_approx_sub_sq_le' hR u hlam hlam1 hε hε' (by linarith)
    _ ≤ 2 ^ (n + 1) * (ε + (1 - lam) * R) ^ 2 * dirichlet u := by
        have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
        gcongr

/-! ## (A2): `L²` convergence of the gradient -/

/-- Neighbourhoods of `1` from the left, unpacked. -/
theorem eventually_nhdsLT_one_iff {P : ℝ → Prop} :
    (∀ᶠ lam in 𝓝[<] (1 : ℝ), P lam)
      ↔ ∃ lam₀ : ℝ, lam₀ < 1 ∧ ∀ lam : ℝ, lam₀ < lam → lam < 1 → P lam := by
  rw [Filter.eventually_iff, mem_nhdsLT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, fun lam h1 h2 => h ⟨h1, h2⟩⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, fun lam hlam => h lam hlam.1 hlam.2⟩

/-- Neighbourhoods of `0` from the right, unpacked. -/
theorem eventually_nhdsGT_zero_iff {P : ℝ → Prop} :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), P ε)
      ↔ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → P ε := by
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, fun ε h1 h2 => h ⟨h1, h2⟩⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, fun ε hε => h ε hε.1 hε.2⟩

/-- A sum over `Fin n` of terms bounded by `c / (n + 1)` is bounded by `c`. -/
theorem sum_fin_le_of_forall_le_div {f : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, f i ≤ c / (n + 1)) : ∑ i, f i ≤ c := by
  calc ∑ i, f i ≤ ∑ _i : Fin n, c / (n + 1) := Finset.sum_le_sum fun i _ => h i
    _ = n * (c / (n + 1)) := by simp
    _ ≤ c := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- (M') for finitely many functions simultaneously. -/
theorem exists_lam_dilate_close_sum {g : Fin n → E → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    {η : ℝ} (hη : 0 < η) :
    ∃ lam₀ : ℝ, lam₀ < 1 ∧ ∀ lam : ℝ, lam₀ < lam → lam < 1 →
      ∑ i, ∫ x, (g i (lam • x) - g i x) ^ 2 ≤ η := by
  have hη' : 0 < η / (n + 1) := by positivity
  have h : ∀ i, ∀ᶠ lam in 𝓝[<] (1 : ℝ),
      ∫ x, (g i (lam • x) - g i x) ^ 2 ≤ η / (n + 1) := fun i => by
    obtain ⟨l, -, hl1, h⟩ := exists_lam_dilate_close (hg i) hη'
    exact eventually_nhdsLT_one_iff.2 ⟨l, hl1, fun lam h1 h2 => h lam h1 h2.le⟩
  obtain ⟨l, hl, h⟩ := eventually_nhdsLT_one_iff.1 (Filter.eventually_all.2 h)
  exact ⟨l, hl, fun lam h1 h2 => sum_fin_le_of_forall_le_div hη.le (h lam h1 h2)⟩

/-- (M) for finitely many functions simultaneously. -/
theorem exists_delta_conv_close_sum {g : Fin n → E → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∑ i, ∫ x, ((mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g i) x - g i x) ^ 2
        ≤ η := by
  have hη' : 0 < η / (n + 1) := by positivity
  have h : ∀ i, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∫ x, ((mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g i) x - g i x) ^ 2
        ≤ η / (n + 1) := fun i => by
    obtain ⟨d, hd, h⟩ := exists_delta_conv_close (hg i) hη'
    exact eventually_nhdsGT_zero_iff.2 ⟨d, hd, h⟩
  obtain ⟨d, hd, h⟩ := eventually_nhdsGT_zero_iff.1 (Filter.eventually_all.2 h)
  exact ⟨d, hd, fun δ h1 h2 => sum_fin_le_of_forall_le_div hη.le (h δ h1 h2)⟩

/-- The pointwise inequality behind (A2): if `G = lam * g'` with `0 ≤ lam ≤ 1`, then
`(a − g)² ≤ 3 ((a − G)² + (g' − g)² + (1 − lam)² g²)`. -/
theorem sq_sub_le_three_mul {a G g g' lam : ℝ} (hG : G = lam * g') (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) :
    (a - g) ^ 2 ≤ 3 * ((a - G) ^ 2 + (g' - g) ^ 2 + (1 - lam) ^ 2 * g ^ 2) := by
  subst hG
  have h1 : (lam * (g' - g)) ^ 2 ≤ (g' - g) ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hlam0 hlam1)
  have h2 : a - g = (a - lam * g') + lam * (g' - g) + (lam - 1) * g := by ring
  have h3 : ((a - lam * g') + lam * (g' - g) + (lam - 1) * g) ^ 2
      ≤ 3 * ((a - lam * g') ^ 2 + (lam * (g' - g)) ^ 2 + ((lam - 1) * g) ^ 2) := by
    nlinarith [sq_nonneg ((a - lam * g') - lam * (g' - g)),
      sq_nonneg (lam * (g' - g) - (lam - 1) * g), sq_nonneg ((a - lam * g') - (lam - 1) * g)]
  have h4 : ((lam - 1) * g) ^ 2 = (1 - lam) ^ 2 * g ^ 2 := by ring
  rw [h2]
  linarith [h3, h1, h4]

/-- **The gradient estimate behind (A2).**  For `x ∈ B_R` the gradient of the approximant is
the vector of mollified components of the weak gradient of `D_lam u`, and
`∫_{B_R} ‖∇(approx u lam ε) − ∇u‖²` is bounded by three explicit error terms. -/
theorem integral_ball_norm_grad_approx_sub_le {R : ℝ} (u : H1 (ball (0 : E) R))
    {lam ε : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 < ε) (hε' : R + ε < R / lam) :
    ∫ x in ball (0 : E) R, ‖classicalGrad (approx u lam ε hlam0) x - u.grad x‖ ^ 2
      ≤ 3 * ((∑ i, ∫ x, ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extGrad (dilate lam hlam0 u) i) x - extGrad (dilate lam hlam0 u) i x) ^ 2)
          + (∑ i, ∫ x, (extGrad u i (lam • x) - extGrad u i x) ^ 2)
          + (1 - lam) ^ 2 * dirichlet u) := by
  have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
  set w := dilate lam hlam0 u with hw
  -- integrability of the three families of error terms
  have hF1 : ∀ i, Integrable (fun x =>
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
        - extGrad w i x) ^ 2) :=
    fun i => integrable_sub_sq (memLp_conv hρ (memLp_extGrad w i)) (memLp_extGrad w i)
  have hF2 : ∀ i, Integrable (fun x => (extGrad u i (lam • x) - extGrad u i x) ^ 2) :=
    fun i => integrable_sub_sq (memLp_comp_smul (memLp_extGrad u i) hlam0) (memLp_extGrad u i)
  have hF3 : ∀ i, Integrable (fun x => (1 - lam) ^ 2 * extGrad u i x ^ 2) :=
    fun i => (memLp_extGrad u i).integrable_sq.const_mul _
  have hF12 : ∀ i, Integrable (fun x =>
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
        - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2) :=
    fun i => (hF1 i).add (hF2 i)
  have hF123 : ∀ i, Integrable (fun x =>
      ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
        - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2
        + (1 - lam) ^ 2 * extGrad u i x ^ 2) :=
    fun i => (hF12 i).add (hF3 i)
  have hΦi : Integrable (fun x => ∑ i,
      (((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
        - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2
        + (1 - lam) ^ 2 * extGrad u i x ^ 2)) :=
    integrable_finset_sum _ fun i _ => hF123 i
  have hΦ0 : ∀ x, 0 ≤ ∑ i,
      (((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
        - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2
        + (1 - lam) ^ 2 * extGrad u i x ^ 2) :=
    fun x => Finset.sum_nonneg fun i _ => by positivity
  -- the pointwise bound on the ball
  have hpt : ∀ x ∈ ball (0 : E) R,
      ‖classicalGrad (approx u lam ε hlam0) x - u.grad x‖ ^ 2
        ≤ 3 * ∑ i, (((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
            - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2
            + (1 - lam) ^ 2 * extGrad u i x ^ 2) := by
    intro x hx
    have hx' : ‖x‖ + ε < R / lam := by
      rw [mem_ball, dist_zero_right] at hx
      linarith
    have hcg : classicalGrad (approx u lam ε hlam0) x
        = WithLp.toLp 2 (fun i =>
            (mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x) :=
      classicalGrad_conv_ext hρ w hx'
    rw [hcg, norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [PiLp.sub_apply]
    rw [← extGrad_apply_of_mem u i hx]
    exact sq_sub_le_three_mul (extGrad_dilate hlam0 u i x) hlam0.le hlam1
  calc ∫ x in ball (0 : E) R, ‖classicalGrad (approx u lam ε hlam0) x - u.grad x‖ ^ 2
      ≤ ∫ x in ball (0 : E) R, 3 * ∑ i,
          (((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
            - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2
            + (1 - lam) ^ 2 * extGrad u i x ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (hΦi.const_mul 3).integrableOn
          (by filter_upwards [ae_restrict_mem measurableSet_ball] with x hx; exact hpt x hx)
    _ ≤ ∫ x, 3 * ∑ i,
          (((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
            - extGrad w i x) ^ 2 + (extGrad u i (lam • x) - extGrad u i x) ^ 2
            + (1 - lam) ^ 2 * extGrad u i x ^ 2) :=
        setIntegral_le_integral (hΦi.const_mul 3)
          (Eventually.of_forall fun x => mul_nonneg (by norm_num) (hΦ0 x))
    _ = 3 * ∑ i, ((∫ x, ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGrad w i) x
            - extGrad w i x) ^ 2) + (∫ x, (extGrad u i (lam • x) - extGrad u i x) ^ 2)
            + (1 - lam) ^ 2 * ∫ x, extGrad u i x ^ 2) := by
        rw [integral_const_mul, integral_finset_sum _ fun i _ => hF123 i]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_add (hF12 i) (hF3 i), integral_add (hF1 i) (hF2 i), integral_const_mul]
    _ = 3 * ((∑ i, ∫ x, ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extGrad (dilate lam hlam0 u) i) x - extGrad (dilate lam hlam0 u) i x) ^ 2)
          + (∑ i, ∫ x, (extGrad u i (lam • x) - extGrad u i x) ^ 2)
          + (1 - lam) ^ 2 * dirichlet u) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_integral_extGrad_sq]

/-- **(A2): gradient convergence.**  For `lam` close to `1` and then `ε` small (depending on
`lam`), `∇(approx u lam ε)` is `η`-close to `∇u` in `L²(B_R)`. -/
theorem exists_approx_grad_close {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R)) {η : ℝ}
    (hη : 0 < η) :
    ∃ lam₀ : ℝ, 1 / 2 ≤ lam₀ ∧ lam₀ < 1 ∧ ∀ lam : ℝ, lam₀ < lam → lam < 1 →
      ∀ hlam0 : 0 < lam, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → R + ε < R / lam ∧
        ∫ x in ball (0 : E) R,
          ‖classicalGrad (approx u lam ε hlam0) x - u.grad x‖ ^ 2 ≤ η := by
  have hη9 : 0 < η / 9 := by positivity
  have hD : 0 ≤ dirichlet u := dirichlet_nonneg u
  -- threshold for the dilation error of the gradient components
  obtain ⟨l₁, hl₁, h₁⟩ := exists_lam_dilate_close_sum (fun i => memLp_extGrad u i) hη9
  -- threshold for the term `(1 - lam)² dirichlet u`
  obtain ⟨l₂, hl₂, h₂⟩ : ∃ l₂ : ℝ, l₂ < 1 ∧ ∀ lam : ℝ, l₂ < lam → lam < 1 →
      (1 - lam) ^ 2 * dirichlet u ≤ η / 9 := by
    set c : ℝ := η / (9 * (dirichlet u + 1)) with hc
    have hc0 : 0 < c := by positivity
    refine ⟨max (1 - c) 0, max_lt (by linarith) one_pos, fun lam h1 h2 => ?_⟩
    have hlam0 : 0 < lam := lt_of_le_of_lt (le_max_right _ _) h1
    have hlamc : 1 - c < lam := lt_of_le_of_lt (le_max_left _ _) h1
    have ht0 : 0 ≤ 1 - lam := by linarith
    have ht1 : 1 - lam ≤ 1 := by linarith
    have htc : 1 - lam ≤ c := by linarith
    have hcD : c * dirichlet u ≤ η / 9 := by
      rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc (1 - lam) ^ 2 * dirichlet u ≤ (1 - lam) * dirichlet u := by
          have : (1 - lam) ^ 2 ≤ 1 - lam := by nlinarith
          exact mul_le_mul_of_nonneg_right this hD
      _ ≤ c * dirichlet u := mul_le_mul_of_nonneg_right htc hD
      _ ≤ η / 9 := hcD
  refine ⟨max (max l₁ l₂) (1 / 2), le_max_right _ _,
    max_lt (max_lt hl₁ hl₂) (by norm_num), fun lam hlam hlam1 hlam0 => ?_⟩
  have hl1 : l₁ < lam := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hlam
  have hl2 : l₂ < lam := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hlam
  set w := dilate lam hlam0 u with hw
  -- threshold for the mollification error of the gradient components of `w`
  obtain ⟨ε₁, hε₁, hε⟩ := exists_delta_conv_close_sum (fun i => memLp_extGrad w i) hη9
  have hRlam : R < R / lam := by
    rw [lt_div_iff₀ hlam0]
    nlinarith
  refine ⟨min ε₁ (R / lam - R), lt_min hε₁ (by linarith), fun ε hε0 hεlt => ?_⟩
  have hε1 : ε < ε₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hε2 : R + ε < R / lam := by
    have := min_le_right ε₁ (R / lam - R)
    linarith
  refine ⟨hε2, ?_⟩
  calc ∫ x in ball (0 : E) R, ‖classicalGrad (approx u lam ε hlam0) x - u.grad x‖ ^ 2
      ≤ 3 * ((∑ i, ∫ x, ((mollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extGrad (dilate lam hlam0 u) i) x - extGrad (dilate lam hlam0 u) i x) ^ 2)
          + (∑ i, ∫ x, (extGrad u i (lam • x) - extGrad u i x) ^ 2)
          + (1 - lam) ^ 2 * dirichlet u) :=
        integral_ball_norm_grad_approx_sub_le u hlam0 hlam1.le hε0 hε2
    _ ≤ 3 * (η / 9 + η / 9 + η / 9) := by
        gcongr
        · exact hε ε hε0 hε1
        · exact h₁ lam hl1 hlam1
        · exact h₂ lam hl2 hlam1
    _ = η := by ring

end RobinCaps.Compact

end
