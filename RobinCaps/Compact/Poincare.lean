import RobinCaps.Compact.WeakGradMollify
import RobinCaps.Compact.Dilation
import RobinCaps.Compact.H1Limit
import RobinCaps.Compact.Contraction

/-!
# Poincaré–Wirtinger on the ball

This file proves Part 2 of `RobinCaps/Compact/PLAN.md`, item `Poincare.lean`:

* `ae_const_of_grad_ae_zero` — an element `u ∈ H¹(B_R)` whose weak gradient vanishes a.e. is
  a.e. equal to a constant.  The mollifications `v_δ := ρ_δ ⋆ ext u` are smooth and, by the
  identity (WG) of `WeakGradMollify.lean`, have vanishing derivative on the ball `B_{R-δ}`
  (the mollified weak gradient is the integral of an a.e.-zero function), hence are constant
  there; since `v_δ → u` a.e. as `δ → 0`
  (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), `u` takes the same value
  at any two points of a full-measure subset of `B_R`.
* `poincare_wirtinger_unit` — **Poincaré–Wirtinger on the unit ball**,
  `mass u ≤ C dirichlet u` for mean-zero `u ∈ H¹(B_1)`, derived from the Rellich property
  (`RellichSeq'`) by the usual compactness argument: a sequence of normalised counterexamples
  is `H¹`-Cauchy along a subsequence, its limit (by `exists_H1_limit`) has zero Dirichlet
  energy, is therefore a.e. constant, has zero mean, hence is zero — contradicting `mass = 1`.
* `poincare_wirtinger_ball` — the same on `B_R`, with the constant `C R²`, by dilation
  (`Dilation.lean`).

The Rellich property itself is proved in `Rellich.lean`; here it is a hypothesis
(`RellichSeq' n 1`), so that this file is independent of the compactness files.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

/-- The Rellich property (an `H¹`-bounded sequence has an `L²(B_R)`-Cauchy subsequence), taken as
a hypothesis here; it is proved in `Rellich.lean`. -/
def RellichSeq' (n : ℕ) (R : ℝ) : Prop :=
  ∀ u : ℕ → H1 (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R),
    (∃ M : ℝ, ∀ k, dirichlet (u k) + mass (u k) ≤ M) →
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ CauchySeq (fun k => toL2 (u (ν k)))

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Zero weak gradient: the mollifications are locally constant -/

section GradZero

variable {R δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}

/-- If the weak gradient of `u` vanishes a.e. on the ball, its zero-extension vanishes a.e. on
`ℝⁿ`. -/
theorem extGrad_ae_zero_of_grad_ae_zero (u : H1 (ball (0 : E) R))
    (h : u.grad =ᵐ[volume.restrict (ball (0 : E) R)] 0) (i : Fin n) :
    extGrad u i =ᵐ[volume] 0 := by
  have h' : ∀ᵐ y ∂(volume : Measure E), y ∈ ball (0 : E) R → u.grad y = (0 : E → E) y :=
    (ae_restrict_iff' measurableSet_ball).mp h
  filter_upwards [h'] with y hy
  by_cases hmem : y ∈ ball (0 : E) R
  · rw [extGrad_apply_of_mem u i hmem, hy hmem]
    simp
  · rw [extGrad_apply_of_not_mem u i hmem]
    simp

/-- The mollification of the zero-extension of an a.e.-vanishing weak gradient vanishes
everywhere. -/
theorem conv_extGrad_eq_zero (u : H1 (ball (0 : E) R))
    (h : u.grad =ᵐ[volume.restrict (ball (0 : E) R)] 0) (i : Fin n) (x : E) :
    (ρ ⋆ extGrad u i) x = 0 := by
  rw [IsMollifier.conv_apply]
  have h0 := extGrad_ae_zero_of_grad_ae_zero u h i
  have h1 : (fun t : E => extGrad u i (x - t)) =ᵐ[volume] fun _ => 0 := by
    have h2 := (Measure.measurePreserving_sub_left (volume : Measure E)
      x).quasiMeasurePreserving.ae_eq_comp h0
    filter_upwards [h2] with t ht
    simpa using ht
  have h3 : (fun t : E => ρ t * extGrad u i (x - t)) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [h1] with t ht
    rw [ht, mul_zero]
  rw [integral_congr_ae h3, integral_zero]

/-- If the weak gradient of `u` vanishes a.e., the mollification `ρ ⋆ ext u` has vanishing
derivative at every point `x` with `‖x‖ + δ < R`. -/
theorem fderiv_conv_ext_eq_zero (hρ : IsMollifier δ ρ) (u : H1 (ball (0 : E) R))
    (h : u.grad =ᵐ[volume.restrict (ball (0 : E) R)] 0) {x : E} (hx : ‖x‖ + δ < R) :
    fderiv ℝ (ρ ⋆ ext u) x = 0 := by
  ext y
  simp only [ContinuousLinearMap.zero_apply]
  conv_lhs => rw [← sum_smul_single y]
  rw [map_sum]
  simp [fderiv_conv_ext hρ u hx, conv_extGrad_eq_zero u h]

/-- If the weak gradient of `u` vanishes a.e., the mollification `ρ ⋆ ext u` is constant on the
ball `B_{R - δ}`. -/
theorem conv_ext_eq_of_grad_ae_zero (hρ : IsMollifier δ ρ) (u : H1 (ball (0 : E) R))
    (h : u.grad =ᵐ[volume.restrict (ball (0 : E) R)] 0) {x y : E} (hx : ‖x‖ + δ < R)
    (hy : ‖y‖ + δ < R) : (ρ ⋆ ext u) x = (ρ ⋆ ext u) y := by
  have hdiff : DifferentiableOn ℝ (ρ ⋆ ext u) (ball (0 : E) (R - δ)) :=
    ((hρ.contDiff_conv (locallyIntegrable_ext u)).differentiable (by simp)).differentiableOn
  refine (isOpen_ball (x := (0 : E)) (ε := R - δ)).is_const_of_fderiv_eq_zero
    (convex_ball (0 : E) (R - δ)).isPreconnected hdiff ?_ ?_ ?_
  · intro z hz
    rw [mem_ball, dist_zero_right] at hz
    exact fderiv_conv_ext_eq_zero hρ u h (by linarith)
  · rw [mem_ball, dist_zero_right]
    linarith
  · rw [mem_ball, dist_zero_right]
    linarith

end GradZero

/-! ## A sequence of mollification scales tending to `0` -/

/-- The mollification scales `R / (k + 2)`. -/
def radiusSeq (R : ℝ) (k : ℕ) : ℝ := R / ((k : ℝ) + 2)

theorem radiusSeq_pos {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < radiusSeq R k := by
  unfold radiusSeq
  positivity

theorem tendsto_radiusSeq (R : ℝ) : Tendsto (radiusSeq R) atTop (𝓝 0) := by
  unfold radiusSeq
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

theorem bump_rIn {δ : ℝ} (hδ : 0 < δ) : (bump (n := n) δ).rIn = δ / 2 := by
  simp [bump, hδ]

/-- **A.e. convergence of the mollifications** `mollifier (R / (k + 2)) ⋆ ext u → ext u`. -/
theorem ae_tendsto_conv_mollifier {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    ∀ᵐ x₀ ∂(volume : Measure E),
      Tendsto (fun k => (mollifier (radiusSeq R k) ⋆ ext u) x₀) atTop (𝓝 (ext u x₀)) := by
  have hφ : Tendsto (fun k => (bump (n := n) (radiusSeq R k)).rOut) atTop (𝓝 0) :=
    (tendsto_radiusSeq R).congr fun k => (bump_rOut (radiusSeq_pos hR k)).symm
  have h'φ : ∀ᶠ k in atTop,
      (bump (n := n) (radiusSeq R k)).rOut ≤ 2 * (bump (n := n) (radiusSeq R k)).rIn := by
    refine Eventually.of_forall fun k => ?_
    rw [bump_rOut (radiusSeq_pos hR k), bump_rIn (radiusSeq_pos hR k)]
    linarith
  unfold mollifier
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) hφ h'φ
    (locallyIntegrable_ext u)

/-! ## Zero weak gradient implies a.e. constant -/

/-- A weak-`H¹` function on the ball with a.e. vanishing weak gradient is a.e. constant. -/
theorem ae_const_of_grad_ae_zero {R : ℝ} (hR : 0 < R) (u : H1 (Metric.ball (0 : E) R))
    (h : u.grad =ᵐ[volume.restrict (Metric.ball (0 : E) R)] 0) :
    ∃ c : ℝ, u.toFun =ᵐ[volume.restrict (Metric.ball (0 : E) R)] fun _ => c := by
  -- The set of points at which the mollifications converge.
  let S : Set E :=
    {x | Tendsto (fun k => (mollifier (radiusSeq R k) ⋆ ext u) x) atTop (𝓝 (ext u x))}
  have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : E) R)), x ∈ S :=
    ae_restrict_of_ae (ae_tendsto_conv_mollifier hR u)
  -- Any two good points of the ball carry the same value of `ext u`.
  have hkey : ∀ x ∈ ball (0 : E) R, x ∈ S → ∀ y ∈ ball (0 : E) R, y ∈ S →
      ext u x = ext u y := by
    intro x hx hxS y hy hyS
    have hxS' : Tendsto (fun k => (mollifier (radiusSeq R k) ⋆ ext u) x) atTop
      (𝓝 (ext u x)) := hxS
    have hyS' : Tendsto (fun k => (mollifier (radiusSeq R k) ⋆ ext u) y) atTop
      (𝓝 (ext u y)) := hyS
    rw [mem_ball, dist_zero_right] at hx hy
    have hev : (fun k => (mollifier (radiusSeq R k) ⋆ ext u) x) =ᶠ[atTop]
        fun k => (mollifier (radiusSeq R k) ⋆ ext u) y := by
      have h1 : ∀ᶠ k in atTop, radiusSeq R k < R - ‖x‖ :=
        (tendsto_radiusSeq R).eventually (eventually_lt_nhds (by linarith))
      have h2 : ∀ᶠ k in atTop, radiusSeq R k < R - ‖y‖ :=
        (tendsto_radiusSeq R).eventually (eventually_lt_nhds (by linarith))
      filter_upwards [h1, h2] with k hk1 hk2
      exact conv_ext_eq_of_grad_ae_zero (isMollifier_mollifier (radiusSeq_pos hR k)) u h
        (by linarith) (by linarith)
    exact tendsto_nhds_unique (hxS'.congr' hev) hyS'
  -- Pick one good point of the ball.
  haveI : (ae (volume.restrict (ball (0 : E) R))).NeBot := by
    refine ae_neBot.mpr fun h0 => ?_
    exact (measure_ball_pos volume (0 : E) hR).ne' (Measure.restrict_eq_zero.mp h0)
  obtain ⟨x₀, hx₀, hx₀S⟩ := ((ae_restrict_mem measurableSet_ball).and hae).exists
  refine ⟨ext u x₀, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball, hae] with x hx hxS
  rw [← ext_apply_of_mem u hx]
  exact hkey x hx hxS x₀ hx₀ hx₀S

/-! ## Elementary estimates for `mass` and `dirichlet` -/

section Algebra

variable {D : Set (EuclideanSpace ℝ (Fin n))}

theorem norm_sub_sq_le_two_mul {F : Type*} [SeminormedAddCommGroup F] (x y : F) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- `dirichlet (u - v) ≤ 2 dirichlet u + 2 dirichlet v`. -/
theorem dirichlet_sub_le (u v : H1 D) :
    dirichlet (u - v) ≤ 2 * dirichlet u + 2 * dirichlet v := by
  rw [dirichlet_sub]
  unfold dirichlet
  have hu : Integrable (fun x => ‖u.grad x‖ ^ 2) (volume.restrict D) :=
    u.grad_memL2.norm.integrable_sq
  have hv : Integrable (fun x => ‖v.grad x‖ ^ 2) (volume.restrict D) :=
    v.grad_memL2.norm.integrable_sq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hu.const_mul 2) (hv.const_mul 2)]
  refine integral_mono ((u.grad_memL2.sub v.grad_memL2).norm.integrable_sq)
    ((hu.const_mul 2).add (hv.const_mul 2)) fun x => ?_
  exact norm_sub_sq_le_two_mul _ _

/-- The integral of a scalar multiple. -/
theorem setIntegral_smul_toFun (c : ℝ) (u : H1 D) :
    ∫ x in D, (c • u).toFun x = c * ∫ x in D, u.toFun x := by
  simp only [H1.smul_toFun, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

end Algebra

section L2Dist

variable {R : ℝ}

/-- The `L²(B_R)` distance is the square root of the mass of the difference. -/
theorem dist_toL2_eq_sqrt_mass_sub (u v : H1 (ball (0 : E) R)) :
    dist (toL2 u) (toL2 v) = Real.sqrt (mass (u - v)) := by
  rw [mass_sub, ← dist_toL2_sq, Real.sqrt_sq dist_nonneg]

theorem dist_toL2_zero_eq_sqrt_mass (u : H1 (ball (0 : E) R)) :
    dist (toL2 u) (toL2 0) = Real.sqrt (mass u) := by
  rw [dist_toL2_eq_sqrt_mass_sub, sub_zero]

/-- The reverse triangle inequality for `√mass`. -/
theorem abs_sqrt_mass_sub_sqrt_mass_le (u v : H1 (ball (0 : E) R)) :
    |Real.sqrt (mass u) - Real.sqrt (mass v)| ≤ Real.sqrt (mass (u - v)) := by
  rw [← dist_toL2_zero_eq_sqrt_mass, ← dist_toL2_zero_eq_sqrt_mass,
    ← dist_toL2_eq_sqrt_mass_sub]
  exact abs_dist_sub_le _ _ _

end L2Dist

/-! ## Poincaré–Wirtinger on the unit ball -/

/-- **Poincaré–Wirtinger on the unit ball** (given compactness). -/
theorem poincare_wirtinger_unit (hrel : RellichSeq' n 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1 (Metric.ball (0 : E) 1),
      (∫ x in Metric.ball (0 : E) 1, u.toFun x) = 0 → mass u ≤ C * dirichlet u := by
  by_contra hcon
  push_neg at hcon
  -- A sequence of counterexamples.
  have hex : ∀ k : ℕ, ∃ u : H1 (ball (0 : E) 1),
      (∫ x in ball (0 : E) 1, u.toFun x) = 0 ∧ ((k : ℝ) + 1) * dirichlet u < mass u :=
    fun k => hcon _ (by positivity)
  choose u hu0 hu using hex
  have hmpos : ∀ k, 0 < mass (u k) := fun k =>
    lt_of_le_of_lt (mul_nonneg (by positivity) (dirichlet_nonneg _)) (hu k)
  -- Normalise to unit mass.
  let w : ℕ → H1 (ball (0 : E) 1) := fun k => (Real.sqrt (mass (u k)))⁻¹ • u k
  have hw_mass : ∀ k, mass (w k) = 1 := by
    intro k
    show mass ((Real.sqrt (mass (u k)))⁻¹ • u k) = 1
    rw [mass_smul, inv_pow, Real.sq_sqrt (hmpos k).le, inv_mul_cancel₀ (hmpos k).ne']
  have hw_dir : ∀ k, dirichlet (w k) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    show dirichlet ((Real.sqrt (mass (u k)))⁻¹ • u k) ≤ 1 / ((k : ℝ) + 1)
    rw [dirichlet_smul, inv_pow, Real.sq_sqrt (hmpos k).le]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [inv_mul_le_iff₀ (hmpos k), mul_one_div, le_div_iff₀ hk]
    have := hu k
    nlinarith
  have hw0 : ∀ k, (∫ x in ball (0 : E) 1, (w k).toFun x) = 0 := by
    intro k
    show (∫ x in ball (0 : E) 1, ((Real.sqrt (mass (u k)))⁻¹ • u k).toFun x) = 0
    rw [setIntegral_smul_toFun, hu0 k, mul_zero]
  have hbdd : ∃ M : ℝ, ∀ k, dirichlet (w k) + mass (w k) ≤ M := by
    refine ⟨2, fun k => ?_⟩
    have h1 := hw_dir k
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    linarith [hw_mass k]
  -- Compactness: an `L²`-Cauchy subsequence.
  obtain ⟨ν, hν, hcauchy⟩ := hrel w hbdd
  have hdir_lim : Tendsto (fun k => dirichlet (w (ν k))) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => dirichlet_nonneg _) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    calc dirichlet (w (ν k)) ≤ 1 / ((ν k : ℝ) + 1) := hw_dir _
      _ ≤ 1 / ((k : ℝ) + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have : k ≤ ν k := hν.id_le k
        have : (k : ℝ) ≤ (ν k : ℝ) := by exact_mod_cast this
        linarith
  -- The subsequence is `H¹`-Cauchy.
  have hH1 : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      mass (w (ν k) - w (ν l)) + dirichlet (w (ν k) - w (ν l)) ≤ η := by
    intro η hη
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.mp hcauchy (Real.sqrt (η / 2)) (by positivity)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hdir_lim) (η / 8) (by positivity)
    refine ⟨max N₁ N₂, fun k l hk hl => ?_⟩
    have hm : mass (w (ν k) - w (ν l)) ≤ η / 2 := by
      have h1 := hN₁ k (le_of_max_le_left hk) l (le_of_max_le_left hl)
      rw [dist_toL2_eq_sqrt_mass_sub, Real.sqrt_lt_sqrt_iff (mass_nonneg _)] at h1
      exact h1.le
    have hd : dirichlet (w (ν k) - w (ν l)) ≤ η / 2 := by
      have h1 := hN₂ k (le_of_max_le_right hk)
      have h2 := hN₂ l (le_of_max_le_right hl)
      rw [Real.dist_eq, sub_zero] at h1 h2
      have h1' := lt_of_abs_lt h1
      have h2' := lt_of_abs_lt h2
      have := dirichlet_sub_le (w (ν k)) (w (ν l))
      linarith
    linarith
  obtain ⟨v, hv⟩ := exists_H1_limit measurableSet_ball (fun k => w (ν k)) hH1
  have hmass_lim : Tendsto (fun k => mass (w (ν k) - v)) atTop (𝓝 0) :=
    squeeze_zero (fun k => mass_nonneg _)
      (fun k => le_add_of_nonneg_right (dirichlet_nonneg _)) hv
  have hdir_lim' : Tendsto (fun k => dirichlet (w (ν k) - v)) atTop (𝓝 0) :=
    squeeze_zero (fun k => dirichlet_nonneg _)
      (fun k => le_add_of_nonneg_left (mass_nonneg _)) hv
  -- (a) The limit has zero Dirichlet energy, hence is a.e. constant.
  have hdv : dirichlet v = 0 := by
    refine le_antisymm ?_ (dirichlet_nonneg v)
    have hlim : Tendsto (fun k => 2 * dirichlet (w (ν k)) + 2 * dirichlet (w (ν k) - v)) atTop
        (𝓝 0) := by
      have := (hdir_lim.const_mul 2).add (hdir_lim'.const_mul 2)
      simpa using this
    refine ge_of_tendsto' hlim fun k => ?_
    have := dirichlet_sub_le (w (ν k)) (w (ν k) - v)
    rwa [sub_sub_cancel] at this
  have hgrad : v.grad =ᵐ[volume.restrict (ball (0 : E) 1)] 0 := by
    have hdv' : ∫ x in ball (0 : E) 1, ‖v.grad x‖ ^ 2 = 0 := hdv
    have h0 : (fun x => ‖v.grad x‖ ^ 2) =ᵐ[volume.restrict (ball (0 : E) 1)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
        v.grad_memL2.norm.integrable_sq).mp hdv'
    filter_upwards [h0] with x hx
    simpa using hx
  obtain ⟨c, hc⟩ := ae_const_of_grad_ae_zero one_pos v hgrad
  -- (b) The limit has zero mean, hence the constant is `0` and the mass is `0`.
  have hint : (∫ x in ball (0 : E) 1, v.toFun x) = 0 := by
    have hlim2 : Tendsto (fun k => ∫ x in ball (0 : E) 1, ((w (ν k)).toFun x - v.toFun x) ^ 2)
        atTop (𝓝 0) := by
      simpa only [mass_sub] using hmass_lim
    have h := tendsto_integral_mul (D := ball (0 : E) 1) (ψ := fun _ => (1 : ℝ))
      (fun k => (w (ν k)).memL2) v.memL2 (memLp_const (1 : ℝ)) hlim2
    simp only [mul_one, hw0] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hc0 : c = 0 := by
    have h1 : (∫ x in ball (0 : E) 1, v.toFun x) = (volume (ball (0 : E) 1)).toReal * c := by
      rw [integral_congr_ae hc, setIntegral_const, smul_eq_mul, measureReal_def]
    rw [hint] at h1
    have hpos : 0 < (volume (ball (0 : E) 1)).toReal :=
      ENNReal.toReal_pos (measure_ball_pos volume (0 : E) one_pos).ne' measure_ball_lt_top.ne
    exact (mul_eq_zero.mp h1.symm).resolve_left hpos.ne'
  have hmv : mass v = 0 := by
    have h2 : (fun x => v.toFun x ^ 2) =ᵐ[volume.restrict (ball (0 : E) 1)]
        fun _ => (0 : ℝ) := by
      filter_upwards [hc] with x hx
      rw [hx, hc0]
      simp
    unfold mass
    rw [integral_congr_ae h2]
    simp
  -- (c) But the limit has unit mass.
  have hmv1 : mass v = 1 := by
    have hlim3 : Tendsto (fun k => Real.sqrt (mass (w (ν k) - v))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hmass_lim
      simpa using this
    have hle : |1 - Real.sqrt (mass v)| ≤ 0 := by
      refine ge_of_tendsto' hlim3 fun k => ?_
      have := abs_sqrt_mass_sub_sqrt_mass_le (w (ν k)) v
      rwa [hw_mass, Real.sqrt_one] at this
    have h1 : Real.sqrt (mass v) = 1 := by
      have := abs_nonpos_iff.mp hle
      linarith
    rw [← Real.sq_sqrt (mass_nonneg v), h1, one_pow]
  rw [hmv] at hmv1
  exact zero_ne_one hmv1

/-! ## Poincaré–Wirtinger on `B_R` -/

/-- **Poincaré–Wirtinger on `B_R`**, with the scaling `C R²`. -/
theorem poincare_wirtinger_ball (hrel : RellichSeq' n 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u := by
  obtain ⟨C, hCpos, hC⟩ := poincare_wirtinger_unit hrel
  refine ⟨C, hCpos, fun R hR u hmean => ?_⟩
  have hRR : R / R = 1 := div_self hR.ne'
  have hwmean : (∫ x in ball (0 : E) 1, (castRadius hRR (dilate R hR u)).toFun x) = 0 := by
    have h1 : (∫ x in ball (0 : E) 1, (castRadius hRR (dilate R hR u)).toFun x)
        = ∫ x in ball (0 : E) 1, u.toFun (R • x) := rfl
    rw [h1, setIntegral_ball_comp_smul u.toFun hR 1, mul_one, hmean, mul_zero]
  have h2 := hC _ hwmean
  rw [mass_castRadius, dirichlet_castRadius, mass_dilate, dirichlet_dilate] at h2
  have hpos : 0 < R⁻¹ ^ n := by positivity
  have h3 : R⁻¹ ^ n * mass u ≤ R⁻¹ ^ n * (C * R ^ 2 * dirichlet u) := by
    calc R⁻¹ ^ n * mass u ≤ C * (R ^ 2 * R⁻¹ ^ n * dirichlet u) := h2
      _ = R⁻¹ ^ n * (C * R ^ 2 * dirichlet u) := by ring
  exact le_of_mul_le_mul_left h3 hpos

end RobinCaps.Compact

end
