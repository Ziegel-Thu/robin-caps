import RobinCaps.Compact.Basic

/-!
# Arzelà–Ascoli: uniformly Lipschitz families are totally bounded in `L²(ball 0 R)`

This file provides the compactness input for the Rellich–Kondrachov theorem of
`RobinCaps/Compact/` (see `PLAN.md`): a sequence of functions on `ℝⁿ` which is *uniformly
bounded* and *uniformly Lipschitz* has totally bounded range in `L²(ball 0 R)`
(`totallyBounded_range_toLp_of_lipschitz`).

The proof restricts the functions to the compact set `closedBall 0 R`, where the set

`{F | (∀ x, |F x| ≤ A) ∧ ∀ x y, dist (F x) (F y) ≤ L * dist x y}`

of bounded continuous functions is closed, uniformly bounded and equicontinuous, hence compact
by `BoundedContinuousFunction.arzela_ascoli₂`; the zero-extension map from bounded continuous
functions on `closedBall 0 R` to `L²(ball 0 R)` is Lipschitz, so it carries this compact set to
a totally bounded set containing the range in question.

The other results of the file supply the two uniform bounds which will be applied to mollified
`L²` functions: `abs_conv_le_sqrt` (a pointwise `L²`-bound for `ρ ⋆ g`) and `lipschitzWith_conv`
(the same for the derivative, giving a Lipschitz constant depending only on `ρ` and `‖g‖₂`).
Both come from the Cauchy–Schwarz inequality `integral_abs_mul_le_sqrt`.

Convolutions are scalar convolutions with respect to Lebesgue measure, as in
`RobinCaps/Compact/Basic.lean`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology BoundedContinuousFunction

namespace RobinCaps.Compact

variable {n : ℕ} {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Cauchy–Schwarz -/

/-- **Cauchy–Schwarz** for two `L²` functions on `ℝⁿ`. -/
theorem integral_abs_mul_le_sqrt {f g : E → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ t, |f t| * |g t| ≤ Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by rwa [h2]
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by rwa [h2]
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure E))
    Real.HolderConjugate.two_two hf' hg'
  have key : ∀ u : E → ℝ,
      (∫ a, ‖u a‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ a, u a ^ 2) := by
    have e : ∀ x : ℝ, ‖x‖ ^ (2 : ℝ) = x ^ 2 := fun x => by
      rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    intro u
    rw [Real.sqrt_eq_rpow]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun a => e (u a))
  calc ∫ t, |f t| * |g t| = ∫ t, ‖f t‖ * ‖g t‖ := by simp [Real.norm_eq_abs]
    _ ≤ (∫ a, ‖f a‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫ a, ‖g a‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := h
    _ = Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by rw [key, key]

/-- `t ↦ g (x - t)` is again in `L²`. -/
theorem memLp_two_sub_left {g : E → ℝ} (hg : MemLp g 2 volume) (x : E) :
    MemLp (fun t => g (x - t)) 2 volume :=
  hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)

/-- Translation (and reflection) invariance of `∫ g²`. -/
theorem integral_sq_sub_left (g : E → ℝ) (x : E) : ∫ t, g (x - t) ^ 2 = ∫ t, g t ^ 2 :=
  integral_sub_left_eq_self (fun t => g t ^ 2) volume x

/-! ## Uniform bounds for mollified `L²` functions -/

/-- Pointwise bound for a mollified `L²` function. -/
theorem abs_conv_le_sqrt (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) (x : E) :
    |(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x|
      ≤ Real.sqrt (∫ t, ρ t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  rw [IsMollifier.conv_apply]
  calc |∫ t, ρ t * g (x - t)| ≤ ∫ t, |ρ t * g (x - t)| := abs_integral_le_integral_abs
    _ = ∫ t, |ρ t| * |g (x - t)| := by simp [abs_mul]
    _ ≤ Real.sqrt (∫ t, ρ t ^ 2) * Real.sqrt (∫ t, g (x - t) ^ 2) :=
        integral_abs_mul_le_sqrt hρ.memLp_two (memLp_two_sub_left hg x)
    _ = Real.sqrt (∫ t, ρ t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by rw [integral_sq_sub_left]

/-- The norm of the derivative of a mollifier is in `L²`. -/
theorem memLp_two_norm_fderiv (hρ : IsMollifier δ ρ) :
    MemLp (fun t => ‖fderiv ℝ ρ t‖) 2 volume :=
  (hρ.contDiff.continuous_fderiv (by norm_num)).norm.memLp_of_hasCompactSupport
    (hρ.hasCompactSupport.fderiv ℝ).norm

/-- The bilinear map used for the derivative of a convolution is bounded as expected. -/
theorem norm_precompL_lsmul_le (u : E →L[ℝ] ℝ) (c : ℝ) :
    ‖((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) u c‖ ≤ ‖u‖ * |c| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [ContinuousLinearMap.precompL_apply]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
  have h : |u w| ≤ ‖u‖ * ‖w‖ := by
    simpa [Real.norm_eq_abs] using u.le_opNorm w
  calc |u w| * |c| ≤ (‖u‖ * ‖w‖) * |c| := by
        exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = ‖u‖ * |c| * ‖w‖ := by ring

/-- The derivative of a mollified `L²` function is bounded by `‖∇ρ‖₂ ‖g‖₂`. -/
theorem norm_fderiv_conv_le (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) (x : E) :
    ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖
      ≤ Real.sqrt (∫ t, ‖fderiv ℝ ρ t‖ ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable one_le_two
  have hd := hρ.hasCompactSupport.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (hρ.contDiff.of_le (by norm_num)) hgl x
  have hcf' : HasCompactSupport (fderiv ℝ ρ) := hρ.hasCompactSupport.fderiv ℝ
  have hcont' : Continuous (fderiv ℝ ρ) := hρ.contDiff.continuous_fderiv (by norm_num)
  have hint : Integrable (fun t => ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E)
      (fderiv ℝ ρ t) (g (x - t))) volume := by
    have := hcf'.convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) hcont' hgl x
    simpa [ConvolutionExistsAt] using this
  have hmul : Integrable (fun t => ‖fderiv ℝ ρ t‖ * |g (x - t)|) volume := by
    have := (memLp_two_norm_fderiv hρ).integrable_mul (memLp_two_sub_left hg x).abs
    simpa [Pi.mul_apply, Real.norm_eq_abs] using this
  rw [hd.fderiv, convolution_def]
  calc ‖∫ t, ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (fderiv ℝ ρ t) (g (x - t))‖
      ≤ ∫ t, ‖((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (fderiv ℝ ρ t) (g (x - t))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖fderiv ℝ ρ t‖ * |g (x - t)| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hmul
          (Eventually.of_forall fun t => ?_)
        exact norm_precompL_lsmul_le _ _
    _ = ∫ t, |‖fderiv ℝ ρ t‖| * |g (x - t)| := by
        simp [abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (∫ t, ‖fderiv ℝ ρ t‖ ^ 2) * Real.sqrt (∫ t, g (x - t) ^ 2) :=
        integral_abs_mul_le_sqrt (memLp_two_norm_fderiv hρ) (memLp_two_sub_left hg x)
    _ = Real.sqrt (∫ t, ‖fderiv ℝ ρ t‖ ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
        rw [integral_sq_sub_left]

/-- A mollified `L²` function is Lipschitz, with constant `‖∇ρ‖₂ ‖g‖₂`. -/
theorem lipschitzWith_conv (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) :
    LipschitzWith
      (Real.toNNReal (Real.sqrt (∫ t, ‖fderiv ℝ ρ t‖ ^ 2) * Real.sqrt (∫ t, g t ^ 2)))
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable one_le_two
  refine lipschitzWith_of_nnnorm_fderiv_le
    ((hρ.contDiff_conv hgl).differentiable (by norm_num)) fun x => ?_
  have hC : (0 : ℝ) ≤ Real.sqrt (∫ t, ‖fderiv ℝ ρ t‖ ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
    positivity
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC]
  exact norm_fderiv_conv_le hρ hg x

/-! ## Continuous functions are in `L²` of the ball -/

/-- Continuous functions are in `L²` of the ball. -/
theorem memLp_ball_of_continuous {R : ℝ} {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Metric.ball (0 : E) R)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (ball_subset_closedBall hx)

/-! ## From bounded continuous functions on the closed ball to `L²(ball 0 R)` -/

open scoped Classical in
/-- The zero-extension of a bounded continuous function on `closedBall 0 R` to all of `ℝⁿ`. -/
def bcExtend (R : ℝ) (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) (x : E) : ℝ :=
  if h : x ∈ closedBall (0 : E) R then F ⟨x, h⟩ else 0

theorem bcExtend_of_mem {R : ℝ} (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) {x : E}
    (hx : x ∈ closedBall (0 : E) R) : bcExtend R F x = F ⟨x, hx⟩ := dif_pos hx

theorem restrict_bcExtend {R : ℝ} (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) :
    (closedBall (0 : E) R).restrict (bcExtend R F) = fun x => F x := by
  funext x
  have hx : (x : E) ∈ closedBall (0 : E) R := x.2
  simp [Set.restrict_apply, bcExtend_of_mem F hx]

theorem continuousOn_bcExtend {R : ℝ} (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) :
    ContinuousOn (bcExtend R F) (closedBall (0 : E) R) := by
  rw [continuousOn_iff_continuous_restrict, restrict_bcExtend]
  exact F.continuous

theorem abs_bcExtend_le {R : ℝ} (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) (x : E) :
    ‖bcExtend R F x‖ ≤ ‖F‖ := by
  by_cases hx : x ∈ closedBall (0 : E) R
  · rw [bcExtend_of_mem F hx]
    exact F.norm_coe_le_norm _
  · simp only [bcExtend, dif_neg hx, norm_zero]
    exact norm_nonneg F

theorem memLp_bcExtend {R : ℝ} (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) :
    MemLp (bcExtend R F) 2 (volume.restrict (ball (0 : E) R)) := by
  have hmeas : AEStronglyMeasurable (bcExtend R F) (volume.restrict (ball (0 : E) R)) :=
    ((continuousOn_bcExtend F).aestronglyMeasurable measurableSet_closedBall).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  exact MemLp.of_bound hmeas ‖F‖ (Eventually.of_forall (abs_bcExtend_le F))

/-- The `L²(ball 0 R)` class of a bounded continuous function on `closedBall 0 R`. -/
def toL2BC (R : ℝ) (F : ↥(closedBall (0 : E) R) →ᵇ ℝ) : L2B n R :=
  (memLp_bcExtend F).toLp (bcExtend R F)

theorem dist_toL2BC_le {R : ℝ} (F G : ↥(closedBall (0 : E) R) →ᵇ ℝ) :
    dist (toL2BC R F) (toL2BC R G)
      ≤ Real.sqrt ((volume (ball (0 : E) R)).toReal) * dist F G := by
  have hvol : (0 : ℝ) ≤ (volume (ball (0 : E) R)).toReal := ENNReal.toReal_nonneg
  have hsq : dist (toL2BC R F) (toL2BC R G) ^ 2
      ≤ (Real.sqrt ((volume (ball (0 : E) R)).toReal) * dist F G) ^ 2 := by
    rw [toL2BC, toL2BC, dist_toLp_sq]
    have h1 : ∫ x in ball (0 : E) R, (bcExtend R F x - bcExtend R G x) ^ 2
        ≤ ∫ _ in ball (0 : E) R, dist F G ^ 2 := by
      refine setIntegral_mono_on
        (((memLp_bcExtend F).sub (memLp_bcExtend G)).integrable_sq)
        (integrable_const _) measurableSet_ball fun x hx => ?_
      have hxc : x ∈ closedBall (0 : E) R := ball_subset_closedBall hx
      rw [bcExtend_of_mem F hxc, bcExtend_of_mem G hxc]
      have hd : |F ⟨x, hxc⟩ - G ⟨x, hxc⟩| ≤ dist F G := by
        rw [← Real.dist_eq]
        exact BoundedContinuousFunction.dist_coe_le_dist _
      calc (F ⟨x, hxc⟩ - G ⟨x, hxc⟩) ^ 2 = |F ⟨x, hxc⟩ - G ⟨x, hxc⟩| ^ 2 := (sq_abs _).symm
        _ ≤ dist F G ^ 2 := by
            have h0 := abs_nonneg (F ⟨x, hxc⟩ - G ⟨x, hxc⟩)
            nlinarith
    refine h1.trans_eq ?_
    rw [setIntegral_const, mul_pow, Real.sq_sqrt hvol, measureReal_def, smul_eq_mul]
  have hd := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq dist_nonneg,
    Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.sqrt ((volume (ball (0 : E) R)).toReal) *
      dist F G)] at hd

theorem lipschitzWith_toL2BC (R : ℝ) :
    LipschitzWith (Real.toNNReal (Real.sqrt ((volume (ball (0 : E) R)).toReal)))
      (toL2BC (n := n) R) := by
  refine LipschitzWith.of_dist_le_mul fun F G => ?_
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact dist_toL2BC_le F G

/-! ## The compact set of bounded, uniformly Lipschitz functions -/

/-- Bounded continuous functions on `closedBall 0 R` bounded by `A` and `L`-Lipschitz. -/
def bcSet (n : ℕ) (R A : ℝ) (L : NNReal) :
    Set (↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) R) →ᵇ ℝ) :=
  {F | (∀ x, |F x| ≤ A) ∧ ∀ x y, dist (F x) (F y) ≤ (L : ℝ) * dist x y}

theorem isClosed_bcSet (n : ℕ) (R A : ℝ) (L : NNReal) : IsClosed (bcSet n R A L) := by
  have h : bcSet n R A L =
      (⋂ x : ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) R), {F | |F x| ≤ A}) ∩
        (⋂ x : ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) R),
          ⋂ y : ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) R),
            {F | dist (F x) (F y) ≤ (L : ℝ) * dist x y}) := by
    ext F
    simp only [bcSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine IsClosed.inter (isClosed_iInter fun x => ?_)
    (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
  · exact isClosed_le (continuous_eval_const x).abs continuous_const
  · exact isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const

theorem isCompact_bcSet (n : ℕ) (R A : ℝ) (L : NNReal) : IsCompact (bcSet n R A L) := by
  refine BoundedContinuousFunction.arzela_ascoli₂ (closedBall (0 : ℝ) A)
    (isCompact_closedBall _ _) (bcSet n R A L) (isClosed_bcSet n R A L) (fun F x hF => ?_) ?_
  · simpa [mem_closedBall_zero_iff, Real.norm_eq_abs] using hF.1 x
  · refine Metric.equicontinuous_of_continuity_modulus (fun t => (L : ℝ) * t) ?_ _ ?_
    · have h : Tendsto (fun t : ℝ => (L : ℝ) * t) (𝓝 0) (𝓝 ((L : ℝ) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using h
    · rintro x y ⟨F, hF⟩
      exact hF.2 x y

/-! ## The main statement -/

/-- A uniformly bounded, uniformly Lipschitz sequence of functions on `ℝⁿ` has totally bounded
range in `L²(ball 0 R)`. -/
theorem totallyBounded_range_toLp_of_lipschitz {R A : ℝ} {L : NNReal} (f : ℕ → E → ℝ)
    (hb : ∀ k x, |f k x| ≤ A) (hL : ∀ k, LipschitzWith L (f k))
    (hm : ∀ k, MemLp (f k) 2 (volume.restrict (Metric.ball (0 : E) R))) :
    TotallyBounded (Set.range fun k => (hm k).toLp (f k)) := by
  classical
  set Fk : ℕ → (↥(closedBall (0 : E) R) →ᵇ ℝ) := fun k =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => f k x, (hL k).continuous.comp continuous_subtype_val⟩ with hFkdef
  have hFk_apply : ∀ k (x : ↥(closedBall (0 : E) R)), Fk k x = f k x := fun k x => rfl
  have hmem : ∀ k, Fk k ∈ bcSet n R A L := by
    intro k
    refine ⟨fun x => by rw [hFk_apply]; exact hb k x, fun x y => ?_⟩
    rw [hFk_apply, hFk_apply]
    simpa [Real.dist_eq, Subtype.dist_eq] using (hL k).dist_le_mul (x : E) (y : E)
  have hTB : TotallyBounded (toL2BC (n := n) R '' bcSet n R A L) :=
    (isCompact_bcSet n R A L).totallyBounded.image (lipschitzWith_toL2BC R).uniformContinuous
  refine TotallyBounded.subset ?_ hTB
  rintro _ ⟨k, rfl⟩
  refine ⟨Fk k, hmem k, ?_⟩
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hxc : x ∈ closedBall (0 : E) R := ball_subset_closedBall hx
  rw [bcExtend_of_mem _ hxc, hFk_apply]

end RobinCaps.Compact

end
