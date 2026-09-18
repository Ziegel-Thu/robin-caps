import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Sharp


open MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

theorem omega_pos (m : ℕ) : 0 < omega m := by
  rw [omega]
  apply ENNReal.toReal_pos
  · exact ne_of_gt (Metric.measure_ball_pos volume _ zero_lt_one)
  · exact ne_of_lt measure_ball_lt_top

theorem omega_ne_zero (m : ℕ) : omega m ≠ 0 := ne_of_gt (omega_pos m)

/-! ## Hemisphere: reduction to the slice integral (Task 1)

For the unit hemisphere in ambient dimension `n = m+1` the manuscript states
`|C| = ω_{m+1}/2`.  We prove the reduction of `(hemisphere m).revolutionVolume`
to the *slice integral* `sphereSlice m = ∫_{-1}^0 (1-s²)^{m/2} ds`, and leave the
sphere-slicing identity `ω_{m+1} = 2 ω_m · sphereSlice m` as an explicit target.
The value of the exposed area is `(m+1) ω_{m+1}/2` (note the factor `m+1`, not
`m`). -/

/-- The hemisphere slice integral `∫_{-1}^0 (1-s²)^{m/2} ds`. -/
noncomputable def sphereSlice (m : ℕ) : ℝ :=
  ∫ s in (-1 : ℝ)..0, (1 - s ^ 2) ^ ((m : ℝ) / 2)

theorem semi_one_pow (m : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 0) :
    (semi 1 s) ^ m = (1 - (s + 1) ^ 2) ^ ((m : ℝ) / 2) := by
  have hx : 0 ≤ 1 - (s + 1) ^ 2 := by
    have h1 : s + 1 ≤ 1 := by linarith [hs.2]
    have h2 : -1 ≤ s + 1 := by linarith [hs.1]
    nlinarith
  rw [semi, Real.sqrt_eq_rpow, ← Real.rpow_natCast _ m, ← Real.rpow_mul hx]
  congr 1
  ring

/-- **Proved reduction.**  The hemisphere volume equals `ω_m` times the slice
integral. -/
theorem hemisphere_revolutionVolume_eq_slice (m : ℕ) :
    (hemisphere m).revolutionVolume = omega m * sphereSlice m := by
  simp only [hemisphere, revolutionVolume, sphereSlice]
  congr 1
  have hcongr : ∫ s in (-1 : ℝ)..0, (semi 1 s) ^ m =
      ∫ s in (-1 : ℝ)..0, (1 - (s + 1) ^ 2) ^ ((m : ℝ) / 2) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs' : s ∈ Set.Icc (-1 : ℝ) 0 := by
      rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hs
    exact semi_one_pow m hs'
  rw [hcongr, intervalIntegral.integral_comp_add_right
    (f := fun u => (1 - u ^ 2) ^ ((m : ℝ) / 2)) 1]
  norm_num
  have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
    (f := fun s => (1 - s ^ 2) ^ ((m : ℝ) / 2))
  simp only [neg_zero] at hneg
  rw [← hneg]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  simp only [neg_sq]

/-- **Target** (recorded as a `Prop`; the proved headline results are in `RobinCaps/Final.lean`).  The sphere-slicing / solid-of-revolution identity
`ω_{m+1} = 2 ω_m ∫_{-1}^0 (1-s²)^{m/2} ds`.  The missing mathlib ingredient is a
real form of the Beta-integral evaluation
`∫_0^1 x^{a-1}(1-x)^{b-1} dx = Γ a Γ b / Γ(a+b)`
(the complex version `Complex.betaIntegral_eq_Gamma_mul_div` and the change of
variables for `∫_0^1 (1-s²)^{m/2} ds` via `s ↦ s²` are available, but the
real-integral identification is not packaged in mathlib). -/
def SphereSlicingTarget (m : ℕ) : Prop :=
  omega (m + 1) = 2 * omega m * sphereSlice m

/-- Conditional hemisphere-volume identity: `|C| = ω_{m+1}/2`. -/
theorem hemisphere_revolutionVolume_eq_of_slicing (m : ℕ) (h : SphereSlicingTarget m) :
    (hemisphere m).revolutionVolume = omega (m + 1) / 2 := by
  rw [hemisphere_revolutionVolume_eq_slice m]
  unfold SphereSlicingTarget at h
  linarith

/-- Conditional statement of the manuscript's `|C| = ω_{m+1}/2`. -/
theorem hemisphere_volume_target_of_slicing (m : ℕ) (h : SphereSlicingTarget m) :
    HemisphereVolumeTarget m := by
  unfold HemisphereVolumeTarget
  exact hemisphere_revolutionVolume_eq_of_slicing m h

/-- The `m = 1` hemisphere volume is `ω₂/2 = π/2` (fully proved). -/
theorem hemisphere_one_revolutionVolume : (hemisphere 1).revolutionVolume = Real.pi / 2 := by
  have hvol := semi_volume_integral 1 one_pos (le_refl 1)
  simp only [hemisphere, revolutionVolume, pow_one]
  rw [omega_one, hvol]
  norm_num [Real.arcsin_one, Real.arcsin_zero]
  ring

/-- The `m = 1` hemisphere exposed area is `(m+1) ω_{m+1}/2 = ω₂ = π`
(fully proved). -/
theorem hemisphere_one_revolutionArea : (hemisphere 1).revolutionArea = Real.pi := by
  have hlat := semi_lateral_integral 1 one_pos (le_refl 1)
  simp only [hemisphere, revolutionArea, lateralArea, terminalArea, tsub_self, pow_zero,
    one_mul]
  rw [omega_one, hlat]
  norm_num [semi, Real.arcsin_one]
  ring


theorem one_sub_pow_sub_one_abs_le (n : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |(1 - v) ^ n - 1| ≤ (n : ℝ) * v := by
  have hle : (1 - v) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hbv : 1 - (n : ℝ) * v ≤ (1 - v) ^ n := by
    have := one_add_mul_le_pow (a := -v) (by linarith : (-2:ℝ) ≤ -v) n
    simpa [sub_eq_add_neg, mul_neg] using this
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

theorem pow_one_sub_sub_linear_bound (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |(1 - u) ^ m - 1 + (m : ℝ) * u| ≤ (m : ℝ) ^ 2 * u ^ 2 := by
  set g : ℝ → ℝ := fun t => (1 - t) ^ m - 1 + (m : ℝ) * t with hg
  set g' : ℝ → ℝ := fun t => (m : ℝ) * (1 - (1 - t) ^ (m - 1)) with hg'
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) u, HasDerivAt g (g' t) t := by
    intro t ht
    rw [hg, hg']
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => (1-t)^m) ((m:ℝ)*(1-t)^(m-1)*(-1)) t := h1.pow m
    have h3 : HasDerivAt (fun t : ℝ => (m:ℝ)*t) (m:ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (m:ℝ)
    have h4 : HasDerivAt (fun t : ℝ => (1-t)^m - 1 + (m:ℝ)*t)
        ((m:ℝ)*(1-t)^(m-1)*(-1) + (m:ℝ)) t := (h2.sub_const 1).add h3
    convert h4 using 1
    ring
  have hcont : ContinuousOn g (Set.Icc (0:ℝ) u) := by
    rw [hg]; fun_prop
  have hg'cont : Continuous g' := by rw [hg']; fun_prop
  have hint : IntervalIntegrable g' volume (0:ℝ) u := hg'cont.intervalIntegrable _ _
  have hFTC : g u - g 0 = ∫ t in (0:ℝ)..u, g' t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0 hcont hderiv hint).symm
  have hg0 : g 0 = 0 := by simp [hg]
  have hgnonneg : 0 ≤ g u := by
    rw [hg]
    have hthis := one_add_mul_le_pow (a := -u) (by linarith : (-2:ℝ) ≤ -u) m
    have hru : (1 + -u) ^ m = (1 - u) ^ m := by ring_nf
    rw [hru] at hthis
    linarith
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) u, g' t ≤ (m:ℝ) * ((m-1 : ℕ) : ℝ) * t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := le_trans ht.2 hu1
    rw [hg']
    have hb : 1 - (((m-1 : ℕ)) : ℝ) * t ≤ (1 - t) ^ (m-1) := by
      have := one_add_mul_le_pow (a := -t) (by linarith : (-2:ℝ) ≤ -t) (m-1)
      simpa [sub_eq_add_neg, mul_neg] using this
    have hstep : 1 - (1-t)^(m-1) ≤ (((m-1 : ℕ)) : ℝ) * t := by linarith
    have hm0 : 0 ≤ (m:ℝ) := by positivity
    nlinarith [hm0, hstep, ht0]
  have hbound2 : IntervalIntegrable (fun t => (m:ℝ) * ((m-1 : ℕ) : ℝ) * t) volume (0:ℝ) u :=
    (by fun_prop : Continuous fun t : ℝ => (m:ℝ) * ((m-1 : ℕ) : ℝ) * t).intervalIntegrable _ _
  have hmono : (∫ t in (0:ℝ)..u, g' t) ≤ ∫ t in (0:ℝ)..u, (m:ℝ) * ((m-1 : ℕ) : ℝ) * t :=
    intervalIntegral.integral_mono_on hu0 hint hbound2 hbound
  have hint2 : (∫ t in (0:ℝ)..u, (m:ℝ) * ((m-1 : ℕ) : ℝ) * t)
      = (m:ℝ) * ((m-1 : ℕ) : ℝ) * u^2/2 := by
    rw [intervalIntegral.integral_const_mul]
    rw [show (∫ t in (0:ℝ)..u, t) = u^2/2 by rw [integral_id]; ring]
    ring
  have hgu : g u = ∫ t in (0:ℝ)..u, g' t := by rw [← hFTC, hg0]; ring
  rw [abs_of_nonneg hgnonneg, hgu]
  calc (∫ t in (0:ℝ)..u, g' t) ≤ (m:ℝ) * ((m-1 : ℕ) : ℝ) * u^2/2 := by
        rw [← hint2]; exact hmono
    _ ≤ (m:ℝ)^2 * u^2 := by
        have hle : ((m-1 : ℕ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
        have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
        have hu2 : (0:ℝ) ≤ u^2 := sq_nonneg u
        have hprod : (m:ℝ) * ((m-1 : ℕ) : ℝ) ≤ (m:ℝ) * m :=
          mul_le_mul_of_nonneg_left hle hm
        nlinarith [hprod, hu2, hm]



theorem sqrt_one_add_sq_eq (t : ℝ) :
    Real.sqrt (1 + t ^ 2) = 1 + t ^ 2 / (Real.sqrt (1 + t ^ 2) + 1) := by
  have hsq : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : Real.sqrt (1 + t ^ 2) + 1 ≠ 0 := by positivity
  have h : Real.sqrt (1 + t ^ 2) - 1 = t ^ 2 / (Real.sqrt (1 + t ^ 2) + 1) := by
    rw [eq_div_iff hpos]
    nlinarith [hsq]
  linarith

theorem integrand_identity (m : ℕ) (hm : 1 ≤ m) (δ c dp : ℝ) :
    (1 - δ * c) ^ (m - 1) * Real.sqrt (1 + (-(δ * dp)) ^ 2) - (1 - δ * c) ^ m
      = δ * c * (1 - δ * c) ^ (m - 1)
        + δ ^ 2 * ((1 - δ * c) ^ (m - 1) * dp ^ 2
            / (Real.sqrt (1 + (δ * dp) ^ 2) + 1)) := by
  have hsq : (-(δ * dp)) ^ 2 = (δ * dp) ^ 2 := by ring
  rw [hsq]
  conv_lhs => rw [sqrt_one_add_sq_eq (δ * dp)]
  have hpow : (1 - δ * c) ^ m = (1 - δ * c) ^ (m - 1) * (1 - δ * c) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [hpow]
  ring

theorem integrand_identity' (m : ℕ) (hm : 1 ≤ m) (δ c dp : ℝ) :
    (1 - δ * c) ^ (m - 1) * Real.sqrt (1 + (-(δ * dp)) ^ 2)
      = (1 - δ * c) ^ m + δ * c * (1 - δ * c) ^ (m - 1)
        + δ ^ 2 * ((1 - δ * c) ^ (m - 1) * dp ^ 2
            / (Real.sqrt (1 + (δ * dp) ^ 2) + 1)) := by
  have h := integrand_identity m hm δ c dp
  linarith [h]

theorem deriv_one_sub (δ : ℝ) (χ χ' : ℝ → ℝ) (K : ℝ)
    (hχderiv : ∀ s ∈ Set.Icc (-K) 0, HasDerivAt χ (χ' s) s) {s : ℝ}
    (hs : s ∈ Set.Icc (-K) 0) :
    deriv (fun s => 1 - δ * χ s) s = -δ * χ' s := by
  have h : HasDerivAt (fun s => 1 - δ * χ s) (0 - δ * χ' s) s := by
    have := (hχderiv s hs).const_mul δ
    simpa using (hasDerivAt_const (x := s) (c := (1:ℝ))).sub this
  rw [h.deriv]
  ring

set_option maxHeartbeats 1600000 in
-- the parametric interval-integral bookkeeping for the decomposition exceeds the default budget
theorem linearization_decomposition (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (χ χ' : ℝ → ℝ) (δ : ℝ)
    (hχderiv : ∀ s ∈ Set.Icc (-K) 0, HasDerivAt χ (χ' s) s)
    (hχ'cont : ContinuousOn χ' (Set.Icc (-K) 0)) :
    revF m K (fun s => 1 - δ * χ s) / omega m
      = (1 - δ * χ 0) ^ m
        + (m : ℝ) * δ * (∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
        + (m : ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
            / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)) := by
  have hKle : (-K : ℝ) ≤ 0 := neg_nonpos.mpr hK.le
  have huIcc : Set.uIcc (-K) 0 = Set.Icc (-K) 0 := Set.uIcc_of_le hKle
  have hχcont : ContinuousOn χ (Set.Icc (-K) 0) :=
    fun s hs => (hχderiv s hs).continuousAt.continuousWithinAt
  set θ : ℝ → ℝ := fun s => 1 - δ * χ s with hθdef
  have hθcont : ContinuousOn θ (Set.Icc (-K) 0) := by
    rw [hθdef]; fun_prop
  have hderivθ_cont : ContinuousOn (fun s => deriv θ s) (Set.Icc (-K) 0) := by
    have hfun : Set.EqOn (fun s => deriv θ s) (fun s => -δ * χ' s) (Set.Icc (-K) 0) := by
      intro s hs
      rw [hθdef]
      exact deriv_one_sub δ χ χ' K hχderiv hs
    exact (continuousOn_const.mul hχ'cont).congr hfun
  let f1 : ℝ → ℝ := fun s => χ s * (θ s) ^ (m - 1)
  let f2 : ℝ → ℝ := fun s => (θ s) ^ (m - 1) * (χ' s) ^ 2 / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)
  have hf1cont : ContinuousOn f1 (Set.Icc (-K) 0) := by
    change ContinuousOn (fun s => χ s * (θ s) ^ (m - 1)) (Set.Icc (-K) 0)
    fun_prop
  have hf2cont : ContinuousOn f2 (Set.Icc (-K) 0) := by
    change ContinuousOn (fun s => (θ s) ^ (m - 1) * (χ' s) ^ 2
      / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)) (Set.Icc (-K) 0)
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      positivity
  rw [← huIcc] at hθcont hderivθ_cont hf1cont hf2cont
  have hint1 : IntervalIntegrable
      (fun s => (θ s)^(m-1) * Real.sqrt (1 + (deriv θ s)^2)) volume (-K) 0 := by
    have hc : ContinuousOn
        (fun s => (θ s)^(m-1) * Real.sqrt (1 + (deriv θ s)^2)) (Set.uIcc (-K) 0) := by
      apply ContinuousOn.mul
      · exact hθcont.pow _
      · apply ContinuousOn.sqrt
        exact continuousOn_const.add (hderivθ_cont.pow 2)
    exact hc.intervalIntegrable
  have hint2 : IntervalIntegrable (fun s => (θ s)^m) volume (-K) 0 :=
    (hθcont.pow _).intervalIntegrable
  have hintf1 : IntervalIntegrable f1 volume (-K) 0 := hf1cont.intervalIntegrable
  have hintf2 : IntervalIntegrable f2 volume (-K) 0 := hf2cont.intervalIntegrable
  have hrev : revF m K θ / omega m
      = θ 0 ^ m + (m:ℝ) * (∫ s in (-K)..0, (θ s)^(m-1) * Real.sqrt (1 + (deriv θ s)^2))
        - (m:ℝ) * (∫ s in (-K)..0, (θ s)^m) := by
    simp only [revF, revLateral, revTerminal, revVolume]
    field_simp [omega_ne_zero m]
    ring
  have hkey : (∫ s in (-K)..0, (θ s)^(m-1) * Real.sqrt (1 + (deriv θ s)^2))
      = (∫ s in (-K)..0, (θ s)^m)
        + ((δ * (∫ s in (-K)..0, f1 s)) + δ^2 * (∫ s in (-K)..0, f2 s)) := by
    have hc1 : (∫ s in (-K)..0, δ * f1 s) = δ * (∫ s in (-K)..0, f1 s) := by
      rw [intervalIntegral.integral_const_mul]
    have hc2 : (∫ s in (-K)..0, δ^2 * f2 s) = δ^2 * (∫ s in (-K)..0, f2 s) := by
      rw [intervalIntegral.integral_const_mul]
    have hpt : ∀ s ∈ Set.uIcc (-K) 0,
        (θ s)^(m-1) * Real.sqrt (1 + (deriv θ s)^2)
          = (θ s)^m + (δ * f1 s + δ^2 * f2 s) := by
      intro s hs
      have hs' : s ∈ Set.Icc (-K) 0 := by rwa [huIcc] at hs
      have hd := deriv_one_sub δ χ χ' K hχderiv hs'
      have hid := integrand_identity' m hm δ (χ s) (χ' s)
      have hθs : θ s = 1 - δ * χ s := by rw [hθdef]
      rw [hd, hθs]
      rw [show (-δ) * χ' s = -(δ * χ' s) by ring]
      rw [hid]
      simp only [f1, f2, hθdef]
      ring
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_add hint2
      ((hintf1.const_mul δ).add (hintf2.const_mul (δ^2)))]
    rw [intervalIntegral.integral_add (hintf1.const_mul δ) (hintf2.const_mul (δ^2))]
    conv_lhs => rw [hc1, hc2]
  have hf1eq : (∫ s in (-K)..0, f1 s) = ∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    simp only [f1, hθdef]
  have hf2eq : (∫ s in (-K)..0, f2 s) = ∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s)^2
      / (Real.sqrt (1 + (δ * χ' s)^2) + 1) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    simp only [f2, hθdef]
  rw [hrev, hkey]
  simp only [hf1eq, hf2eq]
  have hθ0 : θ 0 = 1 - δ * χ 0 := by rw [hθdef]
  rw [hθ0]
  ring


/-- The linearized coefficient `κ = m(χ(0) - ∫_{-K}^0 χ)`. -/
noncomputable def kappa (m : ℕ) (K : ℝ) (χ : ℝ → ℝ) : ℝ :=
  (m : ℝ) * (χ 0 - ∫ s in (-K)..0, χ s)

set_option maxHeartbeats 1600000 in
-- the explicit second-order remainder estimate exceeds the default heartbeat budget
theorem linearization_bound (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (χ χ' : ℝ → ℝ) (M M' : ℝ)
    (hχderiv : ∀ s ∈ Set.Icc (-K) 0, HasDerivAt χ (χ' s) s)
    (hχ'cont : ContinuousOn χ' (Set.Icc (-K) 0))
    (hχnn : ∀ s ∈ Set.Icc (-K) 0, 0 ≤ χ s)
    (hχbound : ∀ s ∈ Set.Icc (-K) 0, χ s ≤ M)
    (hχ'bound : ∀ s ∈ Set.Icc (-K) 0, |χ' s| ≤ M')
    (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∃ C, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ * M ≤ 1 / 2 →
      |revF m K (fun s => 1 - δ * χ s) / omega m - (1 - kappa m K χ * δ)|
        ≤ C * δ ^ 2 := by
  refine ⟨(m:ℝ)^2 * M^2 + (m:ℝ) * M^2 * ((m-1:ℕ):ℝ) * K + (m:ℝ) * M'^2 * K, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ (m:ℝ)^2 * M^2 := by positivity
    have h2 : (0:ℝ) ≤ (m:ℝ) * M^2 * ((m-1:ℕ):ℝ) * K := by positivity
    have h3 : (0:ℝ) ≤ (m:ℝ) * M'^2 * K := by positivity
    linarith
  · intro δ hδ0 hδM
    have hdec := linearization_decomposition m hm K hK χ χ' δ hχderiv hχ'cont
    have hff : revF m K (fun s => 1 - δ * χ s) / omega m - (1 - kappa m K χ * δ)
        = ((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
          + (m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))
          + (m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
              / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)) := by
      rw [hdec, kappa]
      ring
    have hmK0 : (0:ℝ) ≤ (m:ℝ) := by positivity
    have hδ0' : (0:ℝ) ≤ δ := hδ0
    have hχ0mem : (0:ℝ) ∈ Set.Icc (-K) 0 := ⟨by linarith, le_refl 0⟩
    have hP : |(1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0)| ≤ (m:ℝ)^2 * M^2 * δ^2 := by
      have hu0 : 0 ≤ δ * χ 0 := mul_nonneg hδ0 (hχnn 0 hχ0mem)
      have hu1 : δ * χ 0 ≤ 1 := by
        have := hχbound 0 hχ0mem
        nlinarith [hδM, hδ0, hM]
      have h := pow_one_sub_sub_linear_bound m hu0 hu1
      have hc0 : χ 0 ≤ M := hχbound 0 hχ0mem
      have hc0nn : 0 ≤ χ 0 := hχnn 0 hχ0mem
      have hc0sq : (χ 0)^2 ≤ M^2 := by nlinarith [hc0, hc0nn, hM]
      have hsq : (δ * χ 0)^2 ≤ M^2 * δ^2 := by
        rw [show (δ * χ 0)^2 = δ^2 * (χ 0)^2 by ring]
        calc δ^2 * (χ 0)^2 ≤ δ^2 * M^2 := mul_le_mul_of_nonneg_left hc0sq (sq_nonneg δ)
          _ = M^2 * δ^2 := by ring
      calc |(1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0)|
          = |(1 - (δ * χ 0)) ^ m - 1 + (m:ℝ) * (δ * χ 0)| := by ring_nf
        _ ≤ (m:ℝ)^2 * (δ * χ 0)^2 := h
        _ ≤ (m:ℝ)^2 * (M^2 * δ^2) := by gcongr
        _ = (m:ℝ)^2 * M^2 * δ^2 := by ring
    have hIcc_uIcc : Set.uIcc (-K) 0 = Set.Icc (-K) 0 :=
      Set.uIcc_of_le (neg_nonpos.mpr hK.le)
    have hχcont : ContinuousOn χ (Set.Icc (-K) 0) :=
      fun s hs => (hχderiv s hs).continuousAt.continuousWithinAt
    have hθcont : ContinuousOn (fun s => 1 - δ * χ s) (Set.Icc (-K) 0) := by fun_prop
    have hintChi : IntervalIntegrable χ volume (-K) 0 := by
      have hc : ContinuousOn χ (Set.uIcc (-K) 0) := by rw [hIcc_uIcc]; exact hχcont
      exact hc.intervalIntegrable
    have hintA : IntervalIntegrable (fun s => χ s * (1 - δ * χ s) ^ (m - 1)) volume (-K) 0 := by
      have hc : ContinuousOn (fun s => χ s * (1 - δ * χ s) ^ (m - 1)) (Set.uIcc (-K) 0) := by
        rw [hIcc_uIcc]
        exact hχcont.mul (hθcont.pow _)
      exact hc.intervalIntegrable
    have hAdiff : (∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1)) - (∫ s in (-K)..0, χ s)
        = ∫ s in (-K)..0, χ s * ((1 - δ * χ s) ^ (m - 1) - 1) := by
      rw [← intervalIntegral.integral_sub hintA hintChi]
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      ring
    have hAbound : |(∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1)) - (∫ s in (-K)..0, χ s)|
        ≤ M^2 * ((m-1:ℕ):ℝ) * δ * K := by
      rw [hAdiff]
      have hle : ∀ s ∈ Ι (-K) 0, ‖χ s * ((1 - δ * χ s) ^ (m - 1) - 1)‖
          ≤ M^2 * ((m-1:ℕ):ℝ) * δ := by
        intro s hs
        have hsIcc : s ∈ Set.Icc (-K) 0 := by
          rw [Set.uIoc_of_le (neg_nonpos.mpr hK.le)] at hs
          exact ⟨le_of_lt hs.1, hs.2⟩
        have hχs0 : 0 ≤ χ s := hχnn s hsIcc
        have hχsM : χ s ≤ M := hχbound s hsIcc
        have hv0 : 0 ≤ δ * χ s := mul_nonneg hδ0 hχs0
        have hv1 : δ * χ s ≤ 1 := by nlinarith [hδM, hδ0, hχsM, hM]
        have hb := one_sub_pow_sub_one_abs_le (m-1) hv0 hv1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hχs0]
        calc χ s * |(1 - δ * χ s) ^ (m - 1) - 1|
            ≤ χ s * (((m-1:ℕ):ℝ) * (δ * χ s)) :=
              mul_le_mul_of_nonneg_left hb hχs0
          _ ≤ χ s * (((m-1:ℕ):ℝ) * (δ * M)) := by
              have hmm0 : (0:ℝ) ≤ ((m-1:ℕ):ℝ) := by positivity
              gcongr
          _ ≤ M * (((m-1:ℕ):ℝ) * (δ * M)) := by
              have hmm0 : (0:ℝ) ≤ ((m-1:ℕ):ℝ) * (δ * M) := by positivity
              exact mul_le_mul_of_nonneg_right hχsM hmm0
          _ = M^2 * ((m-1:ℕ):ℝ) * δ := by ring
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
      rwa [show |0 - (-K)| = K by rw [abs_of_nonneg (by linarith)]; ring] at h
    have hintB : IntervalIntegrable (fun s => (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
        / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)) volume (-K) 0 := by
      have hc : ContinuousOn (fun s => (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
          / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)) (Set.uIcc (-K) 0) := by
        rw [hIcc_uIcc]
        apply ContinuousOn.div
        · exact (hθcont.pow _).mul (hχ'cont.pow 2)
        · fun_prop
        · intro s hs; positivity
      exact hc.intervalIntegrable
    have hBbound : |(∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
        / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1))| ≤ M'^2 * K := by
      have hle : ∀ s ∈ Ι (-K) 0, ‖(1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
          / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)‖ ≤ M'^2 := by
        intro s hs
        have hsIcc : s ∈ Set.Icc (-K) 0 := by
          rw [Set.uIoc_of_le (neg_nonpos.mpr hK.le)] at hs
          exact ⟨le_of_lt hs.1, hs.2⟩
        have hχs0 : 0 ≤ χ s := hχnn s hsIcc
        have hθle : 1 - δ * χ s ≤ 1 := by nlinarith [mul_nonneg hδ0 hχs0]
        have hθ0 : 0 ≤ 1 - δ * χ s := by nlinarith [hδM, hχbound s hsIcc, hM]
        have hpow0 : 0 ≤ (1 - δ * χ s) ^ (m-1) := pow_nonneg hθ0 _
        have hpow1 : (1 - δ * χ s) ^ (m-1) ≤ 1 := pow_le_one₀ hθ0 hθle
        have hsq : (χ' s)^2 ≤ M'^2 := by
          have h := hχ'bound s hsIcc
          nlinarith [abs_nonneg (χ' s), sq_abs (χ' s), h, hM']
        have hden : 1 ≤ Real.sqrt (1 + (δ * χ' s) ^ 2) + 1 := by
          have : (0:ℝ) ≤ (δ * χ' s)^2 := sq_nonneg _
          have := Real.sqrt_nonneg (1 + (δ * χ' s)^2)
          linarith
        rw [Real.norm_eq_abs, abs_div,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - δ*χ s)^(m-1) * (χ' s)^2),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.sqrt (1 + (δ*χ' s)^2)+1)]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt (1 + (δ*χ' s)^2)+1)]
        have h1 : (1 - δ*χ s)^(m-1) * (χ' s)^2 ≤ 1 * M'^2 := by
          exact mul_le_mul hpow1 hsq (sq_nonneg _) (by norm_num)
        nlinarith [h1, hden]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
      rwa [show |0 - (-K)| = K by rw [abs_of_nonneg (by linarith)]; ring] at h
    rw [hff]
    have htri : |((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
          + (m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))
          + (m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
              / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1))|
        ≤ |(1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0)|
          + |(m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))|
          + |(m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
              / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1))| := by
      have h1 := abs_add_le (((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
          + (m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s)))
        ((m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
              / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1)))
      have h2 := abs_add_le ((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
        ((m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s)))
      linarith
    refine le_trans htri ?_
    have hA2 : |(m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))|
        ≤ (m:ℝ) * δ * (M^2 * ((m-1:ℕ):ℝ) * δ * K) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hmK0 hδ0)]
      exact mul_le_mul_of_nonneg_left hAbound (mul_nonneg hmK0 hδ0)
    have hB2 : |(m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
              / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1))|
        ≤ (m:ℝ) * δ ^ 2 * (M'^2 * K) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hmK0 (sq_nonneg δ))]
      exact mul_le_mul_of_nonneg_left hBbound (mul_nonneg hmK0 (sq_nonneg δ))
    calc |(1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0)|
          + |(m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))|
          + |(m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (χ' s) ^ 2
              / (Real.sqrt (1 + (δ * χ' s) ^ 2) + 1))|
        ≤ (m:ℝ)^2 * M^2 * δ^2 + (m:ℝ) * δ * (M^2 * ((m-1:ℕ):ℝ) * δ * K)
          + (m:ℝ) * δ ^ 2 * (M'^2 * K) := by
          exact add_le_add (add_le_add hP hA2) hB2
      _ = ((m:ℝ)^2 * M^2 + (m:ℝ) * M^2 * ((m-1:ℕ):ℝ) * K + (m:ℝ) * M'^2 * K) * δ^2 := by
          ring


/-! ## Surface-to-volume consistency (Task 3)

The manuscript's `eq:area-volume` and `eq:area-volume-ratio` for a capsule:
with `A = ℋ^m(Γ)`, `V = |C|`, base coefficient `ω = ω_m`, cap length `K` and
total axial length `L`,
`|Ω_R| = ω R^m (L-2KR) + 2 V R^{m+1}`,
`|∂Ω_R| = m ω R^{m-1}(L-2KR) + 2 A R^m`,
and the ratio has the exact remainder
`|∂Ω_R|/|Ω_R| = m/R + 2(A-mV)/(ωL) - 4R(A-mV)(V-ωK)/(ωL(ωL-2ωKR+2VR))`.
This is pure arithmetic. -/

/-- The exact capsule volume parameter `|Ω_R|`. -/
def capsuleVolume (ω L K V R : ℝ) (m : ℕ) : ℝ :=
  ω * R ^ m * (L - 2 * K * R) + 2 * V * R ^ (m + 1)

/-- The exact capsule surface-area parameter `|∂Ω_R|`. -/
def capsuleSurface (ω L K A R : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * ω * R ^ (m - 1) * (L - 2 * K * R) + 2 * A * R ^ m

/-- **Arithmetic core of `eq:area-volume-ratio`** (exact, no `O(R)`). -/
theorem ratio_expansion_arithmetic (m : ℕ) (ω A V K L R : ℝ)
    (hω : ω ≠ 0) (hL : L ≠ 0)
    (hD : ω * L - 2 * ω * K * R + 2 * V * R ≠ 0) :
    ((m : ℝ) * ω * L - 2 * (m : ℝ) * ω * K * R + 2 * A * R)
        / (ω * L - 2 * ω * K * R + 2 * V * R)
      = (m : ℝ) + 2 * R * (A - (m : ℝ) * V) / (ω * L)
        - 4 * R ^ 2 * (A - (m : ℝ) * V) * (V - ω * K)
            / (ω * L * (ω * L - 2 * ω * K * R + 2 * V * R)) := by
  set D : ℝ := ω * L - 2 * ω * K * R + 2 * V * R with hDdef
  have hDnz : D ≠ 0 := by rw [hDdef]; exact hD
  have hLω : ω * L ≠ 0 := mul_ne_zero hω hL
  field_simp
  ring

/-- **`eq:area-volume-ratio`** for the explicit capsule parameters. -/
theorem capsule_surface_volume_ratio (m : ℕ) (hm : 1 ≤ m) (ω A V K L R : ℝ)
    (hω : ω ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0)
    (hD : ω * L - 2 * ω * K * R + 2 * V * R ≠ 0) :
    capsuleSurface ω L K A R m / capsuleVolume ω L K V R m
      = (m : ℝ) / R + 2 * (A - (m : ℝ) * V) / (ω * L)
        - 4 * R * (A - (m : ℝ) * V) * (V - ω * K)
            / (ω * L * (ω * L - 2 * ω * K * R + 2 * V * R)) := by
  have hRpow : R ^ m = R ^ (m - 1) * R := by rw [← pow_succ, Nat.sub_add_cancel hm]
  have hS : capsuleSurface ω L K A R m
      = R ^ (m - 1) * ((m : ℝ) * ω * (L - 2 * K * R) + 2 * A * R) := by
    simp only [capsuleSurface, hRpow]
    ring
  have hV : capsuleVolume ω L K V R m
      = R ^ (m - 1) * (R * (ω * L - 2 * ω * K * R + 2 * V * R)) := by
    simp only [capsuleVolume, hRpow]
    have h2 : R ^ (m + 1) = R ^ (m - 1) * R * R := by
      rw [show m + 1 = (m - 1) + 1 + 1 by omega, pow_succ, pow_succ]
    rw [h2]; ring
  rw [hS, hV]
  have hfac : R ^ (m - 1) * ((m : ℝ) * ω * (L - 2 * K * R) + 2 * A * R)
      / (R ^ (m - 1) * (R * (ω * L - 2 * ω * K * R + 2 * V * R)))
      = (1 / R) * (((m : ℝ) * ω * (L - 2 * K * R) + 2 * A * R)
          / (ω * L - 2 * ω * K * R + 2 * V * R)) := by
    rw [mul_div_mul_left _ _ (pow_ne_zero (m - 1) hR)]
    field_simp
  rw [hfac]
  rw [show (m : ℝ) * ω * (L - 2 * K * R) + 2 * A * R
      = (m : ℝ) * ω * L - 2 * (m : ℝ) * ω * K * R + 2 * A * R by ring]
  rw [ratio_expansion_arithmetic m ω A V K L R hω hL hD]
  field_simp

end

end Cap
end RobinCaps
