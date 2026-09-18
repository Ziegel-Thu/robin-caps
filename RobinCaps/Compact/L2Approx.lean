import RobinCaps.Compact.Basic
import RobinCaps.Compact.Contraction
import RobinCaps.Compact.Dilation

/-!
# `L²`-continuity of mollification and of dilation

This file proves the two approximation statements (M) and (M') of
`RobinCaps/Compact/PLAN.md`:

* `exists_delta_conv_close` — **(M)**: for `g ∈ L²(ℝⁿ)` the mollifications `mollifier δ ⋆ g`
  converge to `g` in `L²(ℝⁿ)` as `δ → 0⁺`;
* `exists_lam_dilate_close` — **(M')**: for `g ∈ L²(ℝⁿ)` the dilations `x ↦ g (lam • x)`
  converge to `g` in `L²(ℝⁿ)` as `lam → 1⁻`.

Both are proved by the standard three-term argument.  One first settles the case of a
*continuous, compactly supported* `g` (`exists_delta_conv_close_of_continuous`,
`exists_lam_dilate_close_of_continuous`), where uniform continuity (`HasCompactSupport.
uniformContinuous_of_continuous`) gives a bound on `|(ρ_δ ⋆ g) x - g x|` resp.
`|g (lam • x) - g x|` that is *uniform in `x`*, while both functions vanish outside one fixed
closed ball; the integral is then at most `(that bound)² · vol (ball)`.  These two statements are
also used elsewhere, which is why they are recorded separately.

The general case follows by density of continuous compactly supported functions in `L²`
(`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), the triangle inequality in `L²`
(`sqrt_integral_sub_sq_le_add`, obtained from the triangle inequality in mathlib's `Lp` space),
and the fact that the two operations are *uniformly bounded* on `L²`: mollification is a
contraction (`integral_conv_sub_sq_le`, file `Contraction.lean`), and dilation by `lam ≥ 1/2` has
norm `lam^{-n/2} ≤ 2^{n/2}` (`integral_comp_smul_sq`, file `Dilation.lean`).

Throughout, `⋆` abbreviates `⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## The `L²` triangle inequality, in integral form -/

/-- The squared `L²(ℝⁿ)` distance of two `Lp` classes is the integral of the squared difference
of representatives. -/
theorem dist_toLp_volume_sq {f g : E → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, (f x - g x) ^ 2 := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg)] with x hx
  rw [hx]
  simp [Pi.sub_apply, pow_two]

/-- `√(∫ (f - g)²)` is the `L²(ℝⁿ)` distance of the classes of `f` and `g`. -/
theorem sqrt_integral_sub_sq_eq_dist {f g : E → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Real.sqrt (∫ x, (f x - g x) ^ 2) = dist (hf.toLp f) (hg.toLp g) := by
  rw [← dist_toLp_volume_sq hf hg, Real.sqrt_sq dist_nonneg]

/-- `√(∫ (f - g)²)` is the real number underlying `eLpNorm (f - g) 2`. -/
theorem sqrt_integral_sub_sq_eq_toReal {f g : E → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Real.sqrt (∫ x, (f x - g x) ^ 2) = (eLpNorm (f - g) 2 volume).toReal := by
  rw [sqrt_integral_sub_sq_eq_dist hf hg, dist_eq_norm, ← MemLp.toLp_sub hf hg, Lp.norm_toLp]

/-- **Minkowski's inequality**, in the form used below. -/
theorem sqrt_integral_sub_sq_le_add {f g h : E → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    Real.sqrt (∫ x, (f x - h x) ^ 2)
      ≤ Real.sqrt (∫ x, (f x - g x) ^ 2) + Real.sqrt (∫ x, (g x - h x) ^ 2) := by
  rw [sqrt_integral_sub_sq_eq_dist hf hh, sqrt_integral_sub_sq_eq_dist hf hg,
    sqrt_integral_sub_sq_eq_dist hg hh]
  exact dist_triangle _ _ _

/-- `∫ (f - g)² ≥ 0`. -/
theorem integral_sub_sq_nonneg (f g : E → ℝ) : 0 ≤ ∫ x, (f x - g x) ^ 2 :=
  integral_nonneg fun _ => sq_nonneg _

/-- `∫ (f - g)² = ∫ (g - f)²`. -/
theorem integral_sub_sq_comm (f g : E → ℝ) :
    ∫ x, (f x - g x) ^ 2 = ∫ x, (g x - f x) ^ 2 := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- Undoing a square root. -/
theorem le_of_sqrt_le_sqrt {A η : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η)
    (h : Real.sqrt A ≤ Real.sqrt η) : A ≤ η := by
  calc A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA).symm
    _ ≤ Real.sqrt η ^ 2 := by gcongr
    _ = η := Real.sq_sqrt hη

/-! ## Two elementary pointwise facts -/

/-- A compactly supported function vanishes outside some closed ball centred at the origin. -/
theorem exists_radius_of_hasCompactSupport {g : E → ℝ} (hs : HasCompactSupport g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : E, M < ‖y‖ → g y = 0 := by
  obtain ⟨M0, hM0⟩ := (IsCompact.isBounded hs).subset_closedBall (0 : E)
  refine ⟨max M0 0, le_max_right _ _, fun y hy => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h1 := hM0 hmem
  rw [mem_closedBall, dist_zero_right] at h1
  exact absurd (h1.trans (le_max_left _ _)) (not_le.2 hy)

/-- **Uniform bound for a mollification.**  If, at the point `x`, the increments `g (x - t) - g x`
are bounded by `α` for `‖t‖ ≤ δ`, then `|(ρ ⋆ g) x - g x| ≤ α`. -/
theorem abs_conv_sub_le {δ : ℝ} {ρ : E → ℝ} (hρ : IsMollifier δ ρ) {g : E → ℝ}
    (hg : LocallyIntegrable g volume) {α : ℝ} (x : E)
    (h : ∀ t : E, ‖t‖ ≤ δ → |g (x - t) - g x| ≤ α) :
    |(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x| ≤ α := by
  have hI : Integrable (fun t : E => ρ t * g (x - t)) volume :=
    hρ.integrable_conv_integrand hg x
  have hc : Integrable (fun t : E => ρ t * g x) volume := hρ.integrable.mul_const (g x)
  have h1 : ∫ t : E, ρ t * g x = g x := by
    rw [integral_mul_const, hρ.integral_eq_one, one_mul]
  have hI2 : Integrable (fun t : E => ρ t * (g (x - t) - g x)) volume := by
    refine (hI.sub hc).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    ring
  have key : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x
      = ∫ t, ρ t * (g (x - t) - g x) := by
    have h2 : ∫ t, ρ t * (g (x - t) - g x)
        = (∫ t, ρ t * g (x - t)) - ∫ t, ρ t * g x := by
      rw [← integral_sub hI hc]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    rw [IsMollifier.conv_apply, h2, h1]
  have hb : ∀ t : E, |ρ t * (g (x - t) - g x)| ≤ ρ t * α := by
    intro t
    by_cases ht : ‖t‖ ≤ δ
    · rw [abs_mul, abs_of_nonneg (hρ.nonneg t)]
      exact mul_le_mul_of_nonneg_left (h t ht) (hρ.nonneg t)
    · rw [hρ.eq_zero_of_lt_norm (not_le.1 ht)]
      simp
  rw [key]
  calc |∫ t, ρ t * (g (x - t) - g x)| ≤ ∫ t, |ρ t * (g (x - t) - g x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t, ρ t * α := integral_mono hI2.abs (hρ.integrable.mul_const α) hb
    _ = α := by rw [integral_mul_const, hρ.integral_eq_one, one_mul]

/-- **Support of a mollification.**  If `g` vanishes outside `closedBall 0 M`, then `ρ ⋆ g`
vanishes outside `closedBall 0 (M + δ)`. -/
theorem conv_eq_zero_of_lt_norm {δ M : ℝ} {ρ : E → ℝ} (hρ : IsMollifier δ ρ) {g : E → ℝ}
    (hg0 : ∀ y : E, M < ‖y‖ → g y = 0) {x : E} (hx : M + δ < ‖x‖) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0 := by
  have hz : (fun t : E => ρ t * g (x - t)) = fun _ : E => (0 : ℝ) := by
    funext t
    by_cases ht : ‖t‖ ≤ δ
    · have hn : M < ‖x - t‖ := lt_of_lt_of_le (by linarith) (norm_sub_norm_le x t)
      rw [hg0 _ hn, mul_zero]
    · rw [hρ.eq_zero_of_lt_norm (not_le.1 ht), zero_mul]
  rw [IsMollifier.conv_apply, hz, integral_zero]

/-- If `|F| ≤ α` everywhere and `F` vanishes outside `closedBall 0 r`, then
`∫ F² ≤ α² vol (closedBall 0 r)`. -/
theorem integral_sq_le_of_bound {F : E → ℝ} (hF : MemLp F 2 volume) {α r : ℝ}
    (hb : ∀ x : E, |F x| ≤ α) (hz : ∀ x : E, r < ‖x‖ → F x = 0) :
    ∫ x, F x ^ 2 ≤ α ^ 2 * (volume (closedBall (0 : E) r)).toReal := by
  have hmeas : MeasurableSet (closedBall (0 : E) r) := measurableSet_closedBall
  have hle : ∀ x : E, F x ^ 2 ≤ (closedBall (0 : E) r).indicator (fun _ => α ^ 2) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : E) r
    · rw [indicator_of_mem hx]
      have h1 : F x ^ 2 = |F x| ^ 2 := (sq_abs _).symm
      nlinarith [abs_nonneg (F x), hb x]
    · rw [indicator_of_notMem hx]
      have hr : r < ‖x‖ := by
        simpa [mem_closedBall, dist_zero_right, not_le] using hx
      rw [hz x hr]
      simp
  have hint : Integrable ((closedBall (0 : E) r).indicator (fun _ => α ^ 2)) volume := by
    rw [integrable_indicator_iff hmeas]
    exact integrableOn_const measure_closedBall_lt_top.ne
  calc ∫ x, F x ^ 2 ≤ ∫ x, (closedBall (0 : E) r).indicator (fun _ => α ^ 2) x :=
        integral_mono hF.integrable_sq hint hle
    _ = α ^ 2 * (volume (closedBall (0 : E) r)).toReal := by
        rw [integral_indicator_const _ hmeas, smul_eq_mul, measureReal_def, mul_comm]

/-! ## (M) for continuous compactly supported functions -/

/-- **(M) for `C_c` functions.**  If `g` is continuous with compact support, the mollifications
`mollifier δ ⋆ g` converge to `g` in `L²(ℝⁿ)` as `δ → 0⁺`. -/
theorem exists_delta_conv_close_of_continuous {g : E → ℝ} (hc : Continuous g)
    (hs : HasCompactSupport g) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∫ x, ((mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) ^ 2 ≤ η := by
  obtain ⟨M, hM, hsupp⟩ := exists_radius_of_hasCompactSupport hs
  have hgL2 : MemLp g 2 volume := hc.memLp_of_hasCompactSupport hs
  have hgloc : LocallyIntegrable g volume := hc.locallyIntegrable
  -- the uniform bound `α` on the increments, chosen so that `α² · vol ≤ η`
  set V : ℝ := (volume (closedBall (0 : E) (M + 1))).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set α : ℝ := Real.sqrt (η / (V + 1)) with hαdef
  have hα : 0 < α := Real.sqrt_pos.2 (by positivity)
  have hα2 : α ^ 2 = η / (V + 1) := Real.sq_sqrt (by positivity)
  have hαV : α ^ 2 * V ≤ η := by
    rw [hα2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- uniform continuity of `g`
  obtain ⟨d, hd, hdg⟩ :=
    Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hc) α hα
  refine ⟨min d 1, lt_min hd one_pos, fun δ hδ hδ' => ?_⟩
  have hδd : δ < d := lt_of_lt_of_le hδ' (min_le_left _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ' (min_le_right _ _)
  have hρ : IsMollifier δ (mollifier (n := n) δ) := isMollifier_mollifier hδ
  set F : E → ℝ := fun x => (mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x
    with hFdef
  have hF : MemLp F 2 volume := (memLp_conv hρ hgL2).sub hgL2
  have hb : ∀ x : E, |F x| ≤ α := by
    intro x
    refine abs_conv_sub_le hρ hgloc x fun t ht => ?_
    have hdist : dist (x - t) x < d := by
      rw [dist_eq_norm]
      simpa using lt_of_le_of_lt ht hδd
    have := hdg hdist
    rw [Real.dist_eq] at this
    exact this.le
  have hz : ∀ x : E, M + 1 < ‖x‖ → F x = 0 := by
    intro x hx
    have h1 : (mollifier (n := n) δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0 :=
      conv_eq_zero_of_lt_norm hρ hsupp (by linarith)
    have h2 : g x = 0 := hsupp x (by linarith)
    rw [hFdef]
    simp [h1, h2]
  exact le_trans (integral_sq_le_of_bound hF hb hz) hαV

/-! ## (M') for continuous compactly supported functions -/

/-- **(M') for `C_c` functions.**  If `g` is continuous with compact support, the dilations
`x ↦ g (lam • x)` converge to `g` in `L²(ℝⁿ)` as `lam → 1⁻`. -/
theorem exists_lam_dilate_close_of_continuous {g : E → ℝ} (hc : Continuous g)
    (hs : HasCompactSupport g) {η : ℝ} (hη : 0 < η) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ lam : ℝ, lam₀ < lam → lam ≤ 1 →
      ∫ x, (g (lam • x) - g x) ^ 2 ≤ η := by
  obtain ⟨M, hM, hsupp⟩ := exists_radius_of_hasCompactSupport hs
  have hgL2 : MemLp g 2 volume := hc.memLp_of_hasCompactSupport hs
  set Q : ℝ := 2 * M + 2 with hQdef
  have hQ : 0 < Q := by rw [hQdef]; linarith
  set V : ℝ := (volume (closedBall (0 : E) Q)).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set α : ℝ := Real.sqrt (η / (V + 1)) with hαdef
  have hα : 0 < α := Real.sqrt_pos.2 (by positivity)
  have hα2 : α ^ 2 = η / (V + 1) := Real.sq_sqrt (by positivity)
  have hαV : α ^ 2 * V ≤ η := by
    rw [hα2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨d, hd, hdg⟩ :=
    Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hc) α hα
  have hdQ : 0 < d / (2 * Q) := by positivity
  refine ⟨max (1 / 2) (1 - d / (2 * Q)), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) (by linarith), fun lam hlam hlam1 => ?_⟩
  have hlam2 : 1 / 2 < lam := lt_of_le_of_lt (le_max_left _ _) hlam
  have hlam3 : 1 - d / (2 * Q) < lam := lt_of_le_of_lt (le_max_right _ _) hlam
  have hlampos : 0 < lam := by linarith
  -- the pointwise bound
  set F : E → ℝ := fun x => g (lam • x) - g x with hFdef
  have hF : MemLp F 2 volume := (memLp_comp_smul hgL2 hlampos).sub hgL2
  have hkey : (1 - lam) * Q < d := by
    have h1 : 1 - lam < d / (2 * Q) := by linarith
    have h2 : (1 - lam) * Q < (d / (2 * Q)) * Q := by
      exact mul_lt_mul_of_pos_right h1 hQ
    have h3 : (d / (2 * Q)) * Q = d / 2 := by field_simp
    rw [h3] at h2
    linarith
  have hb : ∀ x : E, |F x| ≤ α := by
    intro x
    by_cases hx : ‖x‖ ≤ Q
    · have hsm : lam • x - x = (lam - 1) • x := by rw [sub_smul, one_smul]
      have hdist : dist (lam • x) x < d := by
        rw [dist_eq_norm, hsm, norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (by linarith : lam - 1 ≤ 0)]
        have hnn : 0 ≤ ‖x‖ := norm_nonneg x
        have h4 : -(lam - 1) * ‖x‖ ≤ (1 - lam) * Q := by nlinarith
        linarith
      have := hdg hdist
      rw [Real.dist_eq] at this
      exact this.le
    · push_neg at hx
      have h1 : g x = 0 := hsupp x (by linarith)
      have h2 : g (lam • x) = 0 := by
        refine hsupp _ ?_
        have hn : ‖lam • x‖ = lam * ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlampos]
        rw [hn]
        nlinarith
      rw [hFdef]
      simp [h1, h2, hα.le]
  have hz : ∀ x : E, Q < ‖x‖ → F x = 0 := by
    intro x hx
    have h1 : g x = 0 := hsupp x (by linarith)
    have h2 : g (lam • x) = 0 := by
      refine hsupp _ ?_
      have hn : ‖lam • x‖ = lam * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlampos]
      rw [hn]
      nlinarith
    rw [hFdef]
    simp [h1, h2]
  exact le_trans (integral_sq_le_of_bound hF hb hz) hαV

/-! ## (M): mollification converges in `L²(ℝⁿ)` -/

/-- **(M).**  For `g ∈ L²(ℝⁿ)`, the mollifications `mollifier δ ⋆ g` converge to `g` in
`L²(ℝⁿ)` as `δ → 0⁺`. -/
theorem exists_delta_conv_close {g : E → ℝ} (hg : MemLp g 2 volume) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∫ x, ((mollifier δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) ^ 2 ≤ η := by
  set s : ℝ := Real.sqrt η with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hη
  -- approximate `g` by a continuous compactly supported `gc`
  have hεne : ENNReal.ofReal (s / 4) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  obtain ⟨gc, hgcs, hgcle, hgcc, hgcm⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp) hεne
  have hc4 : Real.sqrt (∫ x, (g x - gc x) ^ 2) ≤ s / 4 := by
    rw [sqrt_integral_sub_sq_eq_toReal hg hgcm]
    calc (eLpNorm (g - gc) 2 volume).toReal ≤ (ENNReal.ofReal (s / 4)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hgcle
      _ = s / 4 := ENNReal.toReal_ofReal (by positivity)
  have hc4' : Real.sqrt (∫ x, (gc x - g x) ^ 2) ≤ s / 4 := by
    rwa [← integral_sub_sq_comm]
  -- the mollification of `gc` is close to `gc` for small `δ`
  obtain ⟨δ₀, hδ₀, hmid⟩ :=
    exists_delta_conv_close_of_continuous hgcc hgcs (η := (s / 2) ^ 2) (by positivity)
  refine ⟨δ₀, hδ₀, fun δ hδ hδ' => ?_⟩
  have hρ : IsMollifier δ (mollifier (n := n) δ) := isMollifier_mollifier hδ
  have hSg : MemLp (mollifier (n := n) δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 2 volume :=
    memLp_conv hρ hg
  have hSgc : MemLp (mollifier (n := n) δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gc) 2 volume :=
    memLp_conv hρ hgcm
  -- the middle term
  have hmid' : Real.sqrt (∫ x, ((mollifier (n := n) δ
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gc) x - gc x) ^ 2) ≤ s / 2 := by
    have h := hmid δ hδ hδ'
    calc Real.sqrt (∫ x, ((mollifier (n := n) δ
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gc) x - gc x) ^ 2)
        ≤ Real.sqrt ((s / 2) ^ 2) := Real.sqrt_le_sqrt h
      _ = s / 2 := Real.sqrt_sq (by positivity)
  -- the first term, by the contraction property
  have hfst : Real.sqrt (∫ x, ((mollifier (n := n) δ
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x
        - (mollifier (n := n) δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gc) x) ^ 2)
      ≤ s / 4 :=
    le_trans (Real.sqrt_le_sqrt (integral_conv_sub_sq_le hρ hg hgcm)) hc4
  -- the triangle inequality, twice
  have T1 := sqrt_integral_sub_sq_le_add hSg hSgc hg
  have T2 := sqrt_integral_sub_sq_le_add hSgc hgcm hg
  have hfin : Real.sqrt (∫ x, ((mollifier (n := n) δ
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) ^ 2) ≤ Real.sqrt η := by
    rw [← hsdef]
    linarith
  exact le_of_sqrt_le_sqrt (integral_sub_sq_nonneg _ _) hη.le hfin

/-! ## (M'): dilation is continuous in `L²(ℝⁿ)` -/

/-- **(M').**  For `g ∈ L²(ℝⁿ)`, the dilations `x ↦ g (lam • x)` converge to `g` in `L²(ℝⁿ)`
as `lam → 1⁻`. -/
theorem exists_lam_dilate_close {g : E → ℝ} (hg : MemLp g 2 volume) {η : ℝ} (hη : 0 < η) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧ ∀ lam : ℝ, lam₀ < lam → lam ≤ 1 →
      ∫ x, (g (lam • x) - g x) ^ 2 ≤ η := by
  set s : ℝ := Real.sqrt η with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hη
  set B : ℝ := 1 + Real.sqrt (2 ^ n) with hBdef
  have hB0 : 0 < B := by
    rw [hBdef]
    have := Real.sqrt_nonneg ((2 : ℝ) ^ n)
    linarith
  -- approximate `g` by a continuous compactly supported `gc`
  have hεne : ENNReal.ofReal (s / (2 * B)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  obtain ⟨gc, hgcs, hgcle, hgcc, hgcm⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp) hεne
  have hcB : Real.sqrt (∫ x, (g x - gc x) ^ 2) ≤ s / (2 * B) := by
    rw [sqrt_integral_sub_sq_eq_toReal hg hgcm]
    calc (eLpNorm (g - gc) 2 volume).toReal ≤ (ENNReal.ofReal (s / (2 * B))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hgcle
      _ = s / (2 * B) := ENNReal.toReal_ofReal (by positivity)
  have hcB' : Real.sqrt (∫ x, (gc x - g x) ^ 2) ≤ s / (2 * B) := by
    rwa [← integral_sub_sq_comm]
  -- the dilations of `gc` are close to `gc` for `lam` close to `1`
  obtain ⟨lam₀, hlam₀, hlam₀1, hmid⟩ :=
    exists_lam_dilate_close_of_continuous hgcc hgcs (η := (s / 2) ^ 2) (by positivity)
  refine ⟨max (1 / 2) lam₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) hlam₀1, fun lam hlam hlam1 => ?_⟩
  have hlam2 : 1 / 2 < lam := lt_of_le_of_lt (le_max_left _ _) hlam
  have hlam3 : lam₀ < lam := lt_of_le_of_lt (le_max_right _ _) hlam
  have hlampos : 0 < lam := by linarith
  have hGl : MemLp (fun x : E => g (lam • x)) 2 volume := memLp_comp_smul hg hlampos
  have hGcl : MemLp (fun x : E => gc (lam • x)) 2 volume := memLp_comp_smul hgcm hlampos
  -- the middle term
  have hmid' : Real.sqrt (∫ x, (gc (lam • x) - gc x) ^ 2) ≤ s / 2 := by
    have h := hmid lam hlam3 hlam1
    calc Real.sqrt (∫ x, (gc (lam • x) - gc x) ^ 2)
        ≤ Real.sqrt ((s / 2) ^ 2) := Real.sqrt_le_sqrt h
      _ = s / 2 := Real.sqrt_sq (by positivity)
  -- the first term, by the scaling identity
  have hscale : ∫ x : E, (g (lam • x) - gc (lam • x)) ^ 2
      = lam⁻¹ ^ n * ∫ x : E, (g x - gc x) ^ 2 := by
    simpa using integral_comp_smul_sq (fun y : E => g y - gc y) hlampos
  have hpow : lam⁻¹ ^ n ≤ 2 ^ n := by
    have h1 : lam⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hlampos (by norm_num)]
      linarith
    exact pow_le_pow_left₀ (le_of_lt (inv_pos.2 hlampos)) h1 n
  have hfst : Real.sqrt (∫ x : E, (g (lam • x) - gc (lam • x)) ^ 2)
      ≤ Real.sqrt (2 ^ n) * Real.sqrt (∫ x : E, (g x - gc x) ^ 2) := by
    rw [hscale, Real.sqrt_mul (pow_nonneg (inv_nonneg.2 hlampos.le) n)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hpow) (Real.sqrt_nonneg _)
  -- combine
  have T1 := sqrt_integral_sub_sq_le_add hGl hGcl hg
  have T2 := sqrt_integral_sub_sq_le_add hGcl hgcm hg
  have hBc : B * Real.sqrt (∫ x : E, (g x - gc x) ^ 2) ≤ s / 2 := by
    have h1 : B * Real.sqrt (∫ x : E, (g x - gc x) ^ 2) ≤ B * (s / (2 * B)) :=
      mul_le_mul_of_nonneg_left hcB hB0.le
    have h2 : B * (s / (2 * B)) = s / 2 := by field_simp
    linarith
  have hBexp : B * Real.sqrt (∫ x : E, (g x - gc x) ^ 2)
      = Real.sqrt (∫ x : E, (g x - gc x) ^ 2)
        + Real.sqrt (2 ^ n) * Real.sqrt (∫ x : E, (g x - gc x) ^ 2) := by
    rw [hBdef]; ring
  have hsym : Real.sqrt (∫ x : E, (gc x - g x) ^ 2)
      = Real.sqrt (∫ x : E, (g x - gc x) ^ 2) :=
    congrArg Real.sqrt (integral_sub_sq_comm gc g)
  have hfin : Real.sqrt (∫ x : E, (g (lam • x) - g x) ^ 2) ≤ Real.sqrt η := by
    rw [← hsdef]
    rw [hBexp] at hBc
    linarith
  exact le_of_sqrt_le_sqrt (integral_sub_sq_nonneg _ _) hη.le hfin

end RobinCaps.Compact

end
