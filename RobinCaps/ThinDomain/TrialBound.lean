import RobinCaps.ThinDomain.Trial
import RobinCaps.ThinDomain.BoundaryIntegrable
import RobinCaps.Cap.Main
import RobinCaps.Transverse.OneDim

/-!
# U-TRIALBOUND: the upper-bound side of the thin-domain main theorem

This file proves `lem:cap-upper` (`reference/robin_endcaps_corrected_en.tex`, lines 651–685) and
the trial-function estimates `eq:trial-mass`, `eq:trial-energy` of `sec:proof` (lines 818–828),
discharging the five targets recorded in `RobinCaps/ThinDomain/Trial.lean`.

## The manuscript statements

`lem:cap-upper` (lines 652–662):

```
Regard Ψ_R(z) as a function on 𝒞 independent of s.  Then
  R^{-1}∫_𝒞 |∇_z Ψ_R|²                = O(R),                (eq:upper-gradient)
  J[Ψ_R] − δ_R ‖Ψ_R‖²_{L²(𝒞)}         = β(𝒞) + O(R),          (eq:upper-J)
  R ‖Ψ_R‖²_{L²(𝒞)}                     = O(R).                (eq:upper-mass)
```

with (lines 561–566) `δ_R = R ν_R − m α`, `|δ_R| ≤ CR`, and
`J[U] = α ∫_Γ |U|² dℋ^m − m α ∫_𝒞 |U|²` (`eq:J-definition`), and (lines 818–828)

```
  E_R[𝒯_RF] = a_{β₋,β₊;I_R}[F] + ε_R[F],   |ε_R[F]| ≤ C R S[F],   (eq:trial-energy)
  M[F] ≤ N_R[𝒯_RF] ≤ M[F] + C R S[F].                             (eq:trial-mass)
```

The transverse expansions of `lem:transverse` (lines 441–450) are *hypotheses* here, bundled
into `TransverseExpansionData`:

```
  R² ν_R = m α R + O(R²),                          (eq:nu-expansion)
  ‖Ψ_R − ω_m^{-1/2}‖_{H¹(B_m(1))} ≤ C R,           (eq:Psi-H1)
  d_R := ∫_{B_m(1)} Ψ_R = √ω_m + O(R²),  d_R ≥ ½√ω_m. (eq:d-R)
```

## The new analytic ingredient: a radial trace inequality

The manuscript proves `eq:upper-J` by "taking the trace on the fixed Lipschitz domain `𝒞`".
A trace theorem on a general Lipschitz domain is not available in Mathlib, so the boundary
integral is reduced, through the revolution parametrisation of `Γ`, to spherical means at each
radius `ρ = θ(s) ∈ (0,1]`, and these are estimated by

`ball_trace_ineq_c1` :  `ρ^{m-1} ∫_{S^{m-1}} g(ρω)² dσ(ω) ≤ 2^{m+1} ‖g‖²_{H¹(B_m(1))}`

for every `C¹` function `g` and every `ρ ∈ (0,1]`.  **The weight `ρ^{m-1}` is necessary**: an
unweighted bound `∫_{S^{m-1}} g(ρω)²dσ ≤ C‖g‖²_{H¹}` uniform in `ρ ∈ (0,1]` is false for
`m ≥ 2` (let `ρ ↓ 0`; it would bound `g(0)²` by the `H¹` norm).  The weight is exactly what the
area element `θ^{m-1}√(1+θ'²)` of the surface of revolution supplies, at the cost of the arc
length `∫_{-K}^0 √(1+θ'²) ds` (`capArcLength`, finite by `Cap.Concave.deriv_integrableOn`)
replacing `ℋ^m(Γ)/(mω_m)` in one of the constants.

## Contents

* `one_dim_trace`, `ball_trace_ineq_c1` — the radial trace inequality;
* `integral_sphere_radial_swap` — polar coordinates with the radial integral inside;
* `transLift`, `TransverseExpansionData` — `Ψ_R` and the hypothesis structure;
* `capArcLength`, `capJterm`, `capJForm`, `capEnergyTerm` — the cap-level quantities;
* `cap_upper_gradient`, `cap_mass_le`, `cap_mass_expansion`, `cap_boundary_expansion`,
  `cap_upper_J` — `lem:cap-upper` with explicit constants;
* `capUpperGradientTarget`, `capUpperMassTarget`, `capUpperJTarget` — the `Trial.lean` targets;
* `boundaryEnergy_trialExt`, `renormEnergy_trialH1P`, `massP_trialH1P_caps` — the exact
  splittings of the trial function's energy and mass;
* `trialMassTarget`, `trialEnergyTarget` — `eq:trial-mass` and `eq:trial-energy`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain

noncomputable section

/-! ## 0. Elementary interval-integral comparisons -/

/-- Monotonicity of the integral of a nonnegative continuous function in the interval. -/
theorem intervalIntegral_le_of_subinterval {h : ℝ → ℝ} (hh : Continuous h)
    {a b c d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hnn : ∀ x ∈ Icc c d, 0 ≤ h x) :
    (∫ x in a..b, h x) ≤ ∫ x in c..d, h x := by
  have hcd : c ≤ d := hca.trans (hab.trans hbd)
  have h1 : (0:ℝ) ≤ ∫ x in c..a, h x :=
    intervalIntegral.integral_nonneg hca fun x hx =>
      hnn x ⟨hx.1, hx.2.trans (hab.trans hbd)⟩
  have h2 : (0:ℝ) ≤ ∫ x in b..d, h x :=
    intervalIntegral.integral_nonneg hbd fun x hx =>
      hnn x ⟨hca.trans (hab.trans hx.1), hx.2⟩
  have hI : ∀ u v : ℝ, IntervalIntegrable h volume u v := fun u v => hh.intervalIntegrable u v
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hI c a) (hI a d)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hI a b) (hI b d)
  linarith

/-- If `|f| ≤ h` on `[c, d]` and `a, b ∈ [c, d]`, then `|∫_a^b f| ≤ ∫_c^d h`. -/
theorem abs_intervalIntegral_le {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    {a b c d : ℝ} (hca : c ≤ a) (had : a ≤ d) (hcb : c ≤ b) (hbd : b ≤ d)
    (hfh : ∀ x ∈ Icc c d, |f x| ≤ h x) : |∫ x in a..b, f x| ≤ ∫ x in c..d, h x := by
  have hnn : ∀ x ∈ Icc c d, 0 ≤ h x := fun x hx => le_trans (abs_nonneg _) (hfh x hx)
  have key : ∀ u v : ℝ, u ≤ v → c ≤ u → v ≤ d → |∫ x in u..v, f x| ≤ ∫ x in c..d, h x := by
    intro u v huv hcu hvd
    have h1 : |∫ x in u..v, f x| ≤ ∫ x in u..v, |f x| :=
      intervalIntegral.abs_integral_le_integral_abs huv
    have h2 : (∫ x in u..v, |f x|) ≤ ∫ x in u..v, h x :=
      intervalIntegral.integral_mono_on huv
        (hf.abs.intervalIntegrable (μ := volume) u v)
        (hh.intervalIntegrable (μ := volume) u v)
        (fun x hx => hfh x ⟨hcu.trans hx.1, hx.2.trans hvd⟩)
    exact le_trans h1 (le_trans h2 (intervalIntegral_le_of_subinterval hh hcu huv hvd hnn))
  rcases le_total a b with hab | hab
  · exact key a b hab hca hbd
  · have e : (∫ x in a..b, f x) = -∫ x in b..a, f x := by
      rw [intervalIntegral.integral_symm]
    rw [e, abs_neg]
    exact key b a hab hcb had

/-! ## 1. The one-dimensional weighted trace inequality

For a `C¹` function `φ` on `ℝ` and `0 < ρ ≤ 1`,
`ρ^{m-1} φ(ρ)² ≤ 4·2^{m-1} ∫_0^1 t^{m-1}(φ² + φ'²) dt`.
This is the radial core of `ball_trace_ineq_c1`. -/

set_option maxHeartbeats 1000000 in
theorem one_dim_trace (m : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) :
    ρ ^ (m - 1) * φ ρ ^ 2
      ≤ 4 * 2 ^ (m - 1) * ∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) * (φ t ^ 2 + deriv φ t ^ 2) := by
  set k := m - 1 with hk
  have hcφ : Continuous φ := hφ.continuous
  have hcd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hderiv : ∀ x : ℝ, HasDerivAt φ (deriv φ x) x := fun x =>
    (hφ.differentiable le_rfl x).hasDerivAt
  set q : ℝ → ℝ := fun t => φ t ^ 2 + deriv φ t ^ 2 with hqdef
  have hcq : Continuous q := (hcφ.pow 2).add (hcd.pow 2)
  have hq0 : ∀ t, 0 ≤ q t := fun t => by simp only [hqdef]; positivity
  set w : ℝ → ℝ := fun t => t ^ k * q t with hwdef
  have hcw : Continuous w := (continuous_pow k).mul hcq
  have hw0 : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ w t := fun t ht =>
    mul_nonneg (pow_nonneg ht.1 k) (hq0 t)
  set W : ℝ := ∫ t in (0:ℝ)..1, w t with hWdef
  have hWeq : (∫ t in Ioo (0:ℝ) 1, t ^ k * (φ t ^ 2 + deriv φ t ^ 2)) = W := by
    rw [hWdef, intervalIntegral_eq_integral_Ioo (by norm_num : (0:ℝ) ≤ 1)]
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by norm_num) hw0
  -- the truncated radius
  set ρ' : ℝ := min ρ (1/2) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'half : ρ' ≤ 1/2 := min_le_right _ _
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ2 : ρ ≤ 2 * ρ' := by
    rcases le_total ρ (1/2) with h | h
    · rw [hρ'def, min_eq_left h]; linarith
    · rw [hρ'def, min_eq_right h]; linarith
  set D : ℝ := ∫ r in ρ'..1, q r with hDdef
  have hD0 : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) fun t _ => hq0 t
  -- Claim A : the fundamental theorem of calculus
  have claimA : ∀ t ∈ Icc (1/2:ℝ) 1, φ ρ ^ 2 ≤ φ t ^ 2 + D := by
    intro t ht
    have hFTC : (∫ r in ρ..t, 2 * φ r * deriv φ r) = φ t ^ 2 - φ ρ ^ 2 := by
      have hd : ∀ x ∈ uIcc ρ t, HasDerivAt (fun r => φ r ^ 2) (2 * φ x * deriv φ x) x := by
        intro x _
        have h := (hderiv x).pow 2
        convert h using 1
        ring
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_const.mul hcφ).mul hcd).intervalIntegrable (μ := volume) ρ t)
    have hbound : |∫ r in ρ..t, 2 * φ r * deriv φ r| ≤ D := by
      refine abs_intervalIntegral_le ((continuous_const.mul hcφ).mul hcd) hcq
        hρ'ρ hρ1 (le_trans hρ'half ht.1) ht.2 (fun x _ => ?_)
      have h1 : |2 * φ x * deriv φ x| = 2 * |φ x| * |deriv φ x| := by
        rw [abs_mul, abs_mul]; norm_num
      rw [h1]
      simp only [hqdef]
      nlinarith [sq_nonneg (|φ x| - |deriv φ x|), sq_abs (φ x), sq_abs (deriv φ x)]
    rw [hFTC] at hbound
    have h12 := abs_le.1 hbound
    linarith [h12.1, h12.2]
  -- Claim B : average Claim A over `t ∈ [1/2, 1]`
  have claimB : φ ρ ^ 2 ≤ 2 * (∫ t in (1/2:ℝ)..1, φ t ^ 2) + D := by
    have hmono : (∫ _t in (1/2:ℝ)..1, (φ ρ ^ 2 - D)) ≤ ∫ t in (1/2:ℝ)..1, φ t ^ 2 := by
      refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
        ((hcφ.pow 2).intervalIntegrable (μ := volume) _ _) fun t ht => ?_
      linarith [claimA t ht]
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    nlinarith [hmono]
  -- Claim C
  have claimC : (∫ t in (1/2:ℝ)..1, φ t ^ 2) ≤ 2 ^ k * W := by
    have h1 : (∫ t in (1/2:ℝ)..1, φ t ^ 2) ≤ ∫ t in (1/2:ℝ)..1, 2 ^ k * w t := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((hcφ.pow 2).intervalIntegrable (μ := volume) _ _)
        ((continuous_const.mul hcw).intervalIntegrable (μ := volume) _ _) fun t ht => ?_
      have hge : (1:ℝ) ≤ 2 ^ k * t ^ k := by
        have h2 : (1:ℝ) ≤ (2 * t) ^ k := one_le_pow₀ (by linarith [ht.1])
        rw [mul_pow] at h2
        exact h2
      have hq : φ t ^ 2 ≤ q t := by simp only [hqdef]; nlinarith [sq_nonneg (deriv φ t)]
      simp only [hwdef]
      calc φ t ^ 2 ≤ q t := hq
        _ = 1 * q t := (one_mul _).symm
        _ ≤ (2 ^ k * t ^ k) * q t := mul_le_mul_of_nonneg_right hge (hq0 t)
        _ = 2 ^ k * (t ^ k * q t) := by ring
    have h2 : (∫ t in (1/2:ℝ)..1, 2 ^ k * w t) = 2 ^ k * ∫ t in (1/2:ℝ)..1, w t :=
      intervalIntegral.integral_const_mul _ _
    have h3 : (∫ t in (1/2:ℝ)..1, w t) ≤ W :=
      intervalIntegral_le_of_subinterval hcw (by norm_num) (by norm_num) le_rfl hw0
    have h4 : (0:ℝ) < 2 ^ k := by positivity
    calc (∫ t in (1/2:ℝ)..1, φ t ^ 2) ≤ 2 ^ k * ∫ t in (1/2:ℝ)..1, w t := by rw [← h2]; exact h1
      _ ≤ 2 ^ k * W := by nlinarith [h3, h4]
  -- Claim D
  have claimD : ρ' ^ k * D ≤ W := by
    have h1 : ρ' ^ k * D = ∫ r in ρ'..1, ρ' ^ k * q r :=
      (intervalIntegral.integral_const_mul _ _).symm
    have h2 : (∫ r in ρ'..1, ρ' ^ k * q r) ≤ ∫ r in ρ'..1, w r := by
      refine intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.mul hcq).intervalIntegrable (μ := volume) _ _)
        (hcw.intervalIntegrable (μ := volume) _ _) fun r hr => ?_
      have hle : ρ' ^ k ≤ r ^ k := pow_le_pow_left₀ hρ'pos.le hr.1 k
      simp only [hwdef]
      exact mul_le_mul_of_nonneg_right hle (hq0 r)
    have h3 : (∫ r in ρ'..1, w r) ≤ W :=
      intervalIntegral_le_of_subinterval hcw (by linarith) (by linarith) le_rfl hw0
    linarith [h1 ▸ h2, h3]
  -- assemble
  rw [hWeq]
  have hρk1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ.le hρ1
  have hρk0 : (0:ℝ) ≤ ρ ^ k := pow_nonneg hρ.le k
  have hV0 : (0:ℝ) ≤ 2 ^ k * W := by positivity
  have hkey : ρ ^ k * D ≤ 2 ^ k * W := by
    have h1 : ρ ^ k ≤ 2 ^ k * ρ' ^ k := by
      have h0 : ρ ^ k ≤ (2 * ρ') ^ k := pow_le_pow_left₀ hρ.le hρ2 k
      rwa [mul_pow] at h0
    calc ρ ^ k * D ≤ (2 ^ k * ρ' ^ k) * D := mul_le_mul_of_nonneg_right h1 hD0
      _ = 2 ^ k * (ρ' ^ k * D) := by ring
      _ ≤ 2 ^ k * W := mul_le_mul_of_nonneg_left claimD (by positivity)
  have hfin : φ ρ ^ 2 ≤ 2 * (2 ^ k * W) + D := by linarith [claimB, claimC]
  have s1 : ρ ^ k * φ ρ ^ 2 ≤ ρ ^ k * (2 * (2 ^ k * W) + D) :=
    mul_le_mul_of_nonneg_left hfin hρk0
  have s3 : ρ ^ k * (2 * (2 ^ k * W) + D) = ρ ^ k * (2 * (2 ^ k * W)) + ρ ^ k * D := by ring
  have s4 : ρ ^ k * (2 * (2 ^ k * W)) ≤ 2 * (2 ^ k * W) := by
    calc ρ ^ k * (2 * (2 ^ k * W)) ≤ 1 * (2 * (2 ^ k * W)) :=
          mul_le_mul_of_nonneg_right hρk1 (by linarith)
      _ = 2 * (2 ^ k * W) := one_mul _
  have s5 : 4 * 2 ^ k * W = 4 * (2 ^ k * W) := by ring
  rw [s5]
  linarith [s1, s3, s4, hkey, hV0]

/-! ## 2. From `fderiv` to the classical gradient -/

/-- `|d g_x(v)| ≤ ‖∇g(x)‖ ‖v‖`: the directional derivative is controlled by the classical
gradient.  No differentiability is needed (`fderiv` is `0` otherwise). -/
theorem abs_fderiv_apply_le {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) :
    |fderiv ℝ g x v| ≤ ‖Weak.classicalGrad g x‖ * ‖v‖ := by
  classical
  have hv : (∑ i, (v i) • (EuclideanSpace.single i (1:ℝ))) = v := by
    ext j
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hsum : fderiv ℝ g x v
      = ∑ i, v i * fderiv ℝ g x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← hv]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hin : ⟪Weak.classicalGrad g x, v⟫_ℝ
      = ∑ i, v i * fderiv ℝ g x (EuclideanSpace.single i 1) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Weak.classicalGrad_apply, RCLike.inner_apply]
  rw [hsum, ← hin]
  exact abs_real_inner_le_norm _ _

/-- The radial function `t ↦ g(t ω)` is `C¹` and its derivative is the directional derivative. -/
theorem hasDerivAt_radial {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    (ω : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => g (r • ω)) (fderiv ℝ g (t • ω) ω) t := by
  have h1 : HasDerivAt (fun r : ℝ => r • ω) ω t := by
    simpa using (hasDerivAt_id t).smul_const ω
  exact (hg.differentiable le_rfl (t • ω)).hasFDerivAt.comp_hasDerivAt t h1

theorem contDiff_radial {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g)
    (ω : EuclideanSpace ℝ (Fin n)) : ContDiff ℝ 1 (fun r : ℝ => g (r • ω)) :=
  hg.comp (contDiff_id.smul contDiff_const)

/-! ## 3. Polar coordinates with the radial integral outside -/

/-- Integrability of `(ω, t) ↦ t^{m-1} f(tω)` on `S^{m-1} × (0,1)`. -/
theorem integrable_uncurry_radial (m : ℕ) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) :
    Integrable (Function.uncurry fun (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (t : ℝ) =>
        t ^ (m - 1) * f (t • (ω : EuclideanSpace ℝ (Fin m))))
      ((sphereMeasure m).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  classical
  have hpr : ((sphereMeasure m).prod volume).restrict (univ ×ˢ Ioo (0:ℝ) 1)
      = (sphereMeasure m).prod (volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hcont : Continuous (Function.uncurry fun
      (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (t : ℝ) =>
      t ^ (m - 1) * f (t • (ω : EuclideanSpace ℝ (Fin m)))) := by
    exact (continuous_snd.pow _).mul
      (hf.comp (continuous_snd.smul (continuous_subtype_val.comp continuous_fst)))
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) hf.continuousOn
  have hM0 : (0:ℝ) ≤ max M 0 := le_max_right _ _
  have hfin : ((sphereMeasure m).prod volume) (univ ×ˢ Ioo (0:ℝ) 1) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)
  rw [← hpr]
  haveI : IsFiniteMeasure
      (((sphereMeasure m).prod volume).restrict (univ ×ˢ Ioo (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  refine Integrable.mono' (g := fun _ => max M 0) (integrable_const _)
    hcont.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioo)).2
    (Filter.Eventually.of_forall fun z hz => ?_)
  have ht : z.2 ∈ Ioo (0:ℝ) 1 := hz.2
  have hmem : z.2 • (z.1 : EuclideanSpace ℝ (Fin m))
      ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1,
      mem_sphere_zero_iff_norm.1 z.1.2, mul_one]
    exact ht.2.le
  have hb : ‖f (z.2 • (z.1 : EuclideanSpace ℝ (Fin m)))‖ ≤ max M 0 :=
    (hM _ hmem).trans (le_max_left _ _)
  have hp1 : z.2 ^ (m - 1) ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
  have hp0 : (0:ℝ) ≤ z.2 ^ (m - 1) := pow_nonneg ht.1.le _
  show ‖z.2 ^ (m - 1) * f (z.2 • (z.1 : EuclideanSpace ℝ (Fin m)))‖ ≤ max M 0
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp0]
  calc z.2 ^ (m - 1) * ‖f (z.2 • (z.1 : EuclideanSpace ℝ (Fin m)))‖
      ≤ 1 * (max M 0) := by
        apply mul_le_mul hp1 hb (norm_nonneg _) zero_le_one
    _ = max M 0 := one_mul _

/-- The radial integral `V(ω) = ∫_0^1 t^{m-1} f(tω) dt` is integrable on the sphere. -/
theorem integrable_radial_sphere (m : ℕ) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) :
    Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) * f (t • (ω : EuclideanSpace ℝ (Fin m))))
      (sphereMeasure m) :=
  (integrable_uncurry_radial m hf).integral_prod_left

/-- **Polar coordinates with the radial integral inside**:
`∫_{S^{m-1}} ∫_0^1 t^{m-1} f(tω) dt dσ(ω) = ∫_{B_m(1)} f`. -/
theorem integral_sphere_radial_swap (m : ℕ) (hm : 1 ≤ m)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Continuous f) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) * f (t • (ω : EuclideanSpace ℝ (Fin m))))
        ∂(sphereMeasure m))
      = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f y := by
  have hint : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (hf.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).mono_set ball_subset_closedBall
  rw [integral_ball_polar m hm 1 one_pos f hint]
  rw [integral_integral_swap (integrable_uncurry_radial m hf)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  rw [← MeasureTheory.integral_const_mul]

/-! ## 4. The radial trace inequality on the unit ball -/

/-- **The trace inequality on the sphere of radius `ρ` inside the unit ball**, for `C¹`
functions, with the weight `ρ^{m-1}` which makes the constant uniform in `ρ ∈ (0,1]`:
`ρ^{m-1} ∫_{S^{m-1}} g(ρω)² dσ(ω) ≤ 2^{m+1} ‖g‖²_{H¹(B_m(1))}`. -/
theorem ball_trace_ineq_c1 (m : ℕ) (hm : 1 ≤ m) {g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hg : ContDiff ℝ 1 g) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ (m - 1) * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m))
      ≤ 2 ^ (m + 1) * ((∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, g y ^ 2)
          + ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
              ‖Weak.classicalGrad g y‖ ^ 2) := by
  have hcg : Continuous (Weak.classicalGrad g) := Weak.continuous_classicalGrad g hg
  have hfc : Continuous (fun y => g y ^ 2 + ‖Weak.classicalGrad g y‖ ^ 2) :=
    (hg.continuous.pow 2).add (hcg.norm.pow 2)
  -- pointwise trace bound on each ray
  have key : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      ρ ^ (m - 1) * g (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
        ≤ 4 * 2 ^ (m - 1) * ∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) *
            ((fun y => g y ^ 2 + ‖Weak.classicalGrad g y‖ ^ 2)
              (t • (ω : EuclideanSpace ℝ (Fin m)))) := by
    intro ω
    have hφ : ContDiff ℝ 1 (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) :=
      contDiff_radial hg _
    have h1 := one_dim_trace m hφ hρ hρ1
    refine h1.trans ?_
    have hmono : (∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) *
          ((fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) t ^ 2
            + deriv (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) t ^ 2))
        ≤ ∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) *
            ((fun y => g y ^ 2 + ‖Weak.classicalGrad g y‖ ^ 2)
              (t • (ω : EuclideanSpace ℝ (Fin m)))) := by
      have hc1 : Continuous (fun t : ℝ => t ^ (m - 1) *
          ((fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) t ^ 2
            + deriv (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) t ^ 2)) :=
        (continuous_pow _).mul ((hφ.continuous.pow 2).add ((hφ.continuous_deriv le_rfl).pow 2))
      have hc2 : Continuous (fun t : ℝ => t ^ (m - 1) *
          ((fun y => g y ^ 2 + ‖Weak.classicalGrad g y‖ ^ 2)
            (t • (ω : EuclideanSpace ℝ (Fin m))))) :=
        (continuous_pow _).mul
          (hfc.comp (continuous_id.smul continuous_const))
      refine setIntegral_mono_on
        (hc1.continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))
          |>.mono_set Ioo_subset_Icc_self)
        (hc2.continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))
          |>.mono_set Ioo_subset_Icc_self)
        measurableSet_Ioo fun t ht => ?_
      have hd : deriv (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) t
          = fderiv ℝ g (t • (ω : EuclideanSpace ℝ (Fin m))) (ω : EuclideanSpace ℝ (Fin m)) :=
        (hasDerivAt_radial hg _ t).deriv
      have hb : |fderiv ℝ g (t • (ω : EuclideanSpace ℝ (Fin m)))
            (ω : EuclideanSpace ℝ (Fin m))|
          ≤ ‖Weak.classicalGrad g (t • (ω : EuclideanSpace ℝ (Fin m)))‖ := by
        have h := abs_fderiv_apply_le g (t • (ω : EuclideanSpace ℝ (Fin m)))
          (ω : EuclideanSpace ℝ (Fin m))
        rwa [mem_sphere_zero_iff_norm.1 ω.2, mul_one] at h
      have hsq : deriv (fun r : ℝ => g (r • (ω : EuclideanSpace ℝ (Fin m)))) t ^ 2
          ≤ ‖Weak.classicalGrad g (t • (ω : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
        rw [hd, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have ht0 : (0:ℝ) ≤ t ^ (m - 1) := pow_nonneg ht.1.le _
      simp only []
      nlinarith [hsq, ht0]
    have h4 : (0:ℝ) ≤ 4 * 2 ^ (m - 1) := by positivity
    exact mul_le_mul_of_nonneg_left hmono h4
  -- integrate the pointwise bound over the sphere
  have hLint : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ρ ^ (m - 1) * g (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2) (sphereMeasure m) := by
    refine Integrable.const_mul ?_ _
    have hc : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        g (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2) :=
      (hg.continuous.comp (continuous_const.smul continuous_subtype_val)).pow 2
    have h := hc.continuousOn.integrableOn_compact (μ := sphereMeasure m) isCompact_univ
    rwa [integrableOn_univ] at h
  have hRint : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      4 * 2 ^ (m - 1) * ∫ t in Ioo (0:ℝ) 1, t ^ (m - 1) *
        ((fun y => g y ^ 2 + ‖Weak.classicalGrad g y‖ ^ 2)
          (t • (ω : EuclideanSpace ℝ (Fin m))))) (sphereMeasure m) :=
    ((integrable_radial_sphere m hfc)).const_mul _
  have hmain := integral_mono hLint hRint key
  rw [integral_const_mul, integral_const_mul, integral_sphere_radial_swap m hm hfc] at hmain
  have hsplit : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (g y ^ 2 + ‖Weak.classicalGrad g y‖ ^ 2))
      = (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, g y ^ 2)
        + ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖Weak.classicalGrad g y‖ ^ 2 := by
    refine integral_add ?_ ?_
    · exact ((hg.continuous.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).mono_set ball_subset_closedBall
    · exact ((hcg.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).mono_set ball_subset_closedBall
  rw [hsplit] at hmain
  have hpow : (4:ℝ) * 2 ^ (m - 1) = 2 ^ (m + 1) := by
    have : m - 1 + 2 = m + 1 := by omega
    calc (4:ℝ) * 2 ^ (m - 1) = 2 ^ (m - 1 + 2) := by ring
      _ = 2 ^ (m + 1) := by rw [this]
  rwa [hpow] at hmain

/-! ## 5. The lifted transverse ground state `Ψ_R` -/

variable {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- `Ψ_R(y) = R^{m/2} ψ_R(R y)` of `eq:scaled-groundstate`, as a function of the transverse
variable alone.  `capGroundLift` of `Trial.lean` is its lift to the cap. -/
def transLift (m : ℕ) (R : ℝ) (ψ : TransH1 m R) : EuclideanSpace ℝ (Fin m) → ℝ :=
  fun y => R ^ ((m : ℝ) / 2) * ψ.toFun (R • y)

theorem capGroundLift_eq_transLift (m : ℕ) (R : ℝ) (ψ : TransH1 m R) :
    capGroundLift m R ψ = fun p : CapSpace m => transLift m R ψ p.2 := rfl

theorem contDiff_transLift {ψ : TransH1 m R} (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) :
    ContDiff ℝ 1 (transLift m R ψ) :=
  contDiff_const.mul (hψ.comp (contDiff_const.smul contDiff_id))

/-- `(R^{m/2})² = R^m`. -/
theorem sq_rpow_half (m : ℕ) {R : ℝ} (hR : 0 < R) : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := by
  have hc : (m : ℝ) / 2 * ((2:ℕ) : ℝ) = (m : ℝ) := by push_cast; ring
  rw [← Real.rpow_natCast (R ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hR.le, hc, Real.rpow_natCast]

theorem transLift_sq (m : ℕ) {R : ℝ} (hR : 0 < R) (ψ : TransH1 m R)
    (y : EuclideanSpace ℝ (Fin m)) :
    transLift m R ψ y ^ 2 = R ^ m * ψ.toFun (R • y) ^ 2 := by
  rw [transLift, mul_pow, sq_rpow_half m hR]

/-- The classical gradient of the lifted profile. -/
theorem classicalGrad_transLift {ψ : TransH1 m R}
    (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) (y : EuclideanSpace ℝ (Fin m)) :
    Weak.classicalGrad (transLift m R ψ) y
      = (R ^ ((m : ℝ) / 2) * R) • Weak.classicalGrad (fun z => ψ.toFun z) (R • y) := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => R • y)
      (R • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) y :=
    (hasFDerivAt_id y).const_smul R
  have h2 : HasFDerivAt (fun z => ψ.toFun z)
      (fderiv ℝ (fun z => ψ.toFun z) (R • y)) (R • y) :=
    (hψ.differentiable le_rfl (R • y)).hasFDerivAt
  have h4 : HasFDerivAt (transLift m R ψ)
      (R ^ ((m : ℝ) / 2) • ((fderiv ℝ (fun z => ψ.toFun z) (R • y)).comp
        (R • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))))) y := by
    simpa [transLift, Function.comp_def] using (h2.comp y h1).const_mul (R ^ ((m : ℝ) / 2))
  ext i
  rw [Weak.classicalGrad_apply, h4.fderiv]
  simp [Weak.classicalGrad_apply, mul_assoc]

theorem norm_classicalGrad_transLift_sq {ψ : TransH1 m R} (hR : 0 < R)
    (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) (y : EuclideanSpace ℝ (Fin m)) :
    ‖Weak.classicalGrad (transLift m R ψ) y‖ ^ 2
      = R ^ m * R ^ 2 * ‖Weak.classicalGrad (fun z => ψ.toFun z) (R • y)‖ ^ 2 := by
  rw [classicalGrad_transLift hψ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow,
    sq_rpow_half m hR]

/-- The transverse gradient of the lifted cap function is the classical gradient of `Ψ_R`. -/
theorem gradZP_capGroundLift {ψ : TransH1 m R}
    (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) (p : CapSpace m) :
    gradZP (capGroundLift m R ψ) p = Weak.classicalGrad (transLift m R ψ) p.2 := by
  have h := gradZP_axialTensor (g := fun _ : ℝ => (1:ℝ)) (g' := 0) (p := p)
    (hasDerivAt_const p.1 (1:ℝ)) (contDiff_transLift (ψ := ψ) hψ)
  simpa [capGroundLift_eq_transLift] using h

/-- `‖Ψ_R‖_{L²(B_m(1))} = 1` (from `‖ψ_R‖_{L²(B_m(R))} = 1`). -/
theorem integral_transLift_sq (hR : 0 < R) (gsr : TransverseGroundStateReg m α R bd) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y ^ 2) = 1 := by
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR
    (fun z => gsr.psi.toFun z ^ 2)
  rw [mul_one] at h
  have h2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y ^ 2)
      = R ^ m * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, gsr.psi.toFun (R • y) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun y _ => transLift_sq m hR gsr.psi y
  rw [h2, ← h]
  exact gsr.normalized

/-! ## 6. The hypothesis structure: the transverse expansions of `lem:transverse` -/

/-- **The transverse expansions** `eq:nu-expansion`, `eq:Psi-H1`, `eq:d-R` of `lem:transverse`,
with one explicit constant `Cexp`, together with the boundary-form compatibility
`bd(ψ_R, ψ_R) = ∫_{∂B_m(R)} ψ_R²`.

These are *not* proved here (`lem:transverse` is a separate result; for `m = 1` its statements
are `RobinCaps.Transverse.nuR_expansion`, `PsiH1Target`, `dRTarget`). -/
structure TransverseExpansionData (m : ℕ) (α R : ℝ)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gsr : TransverseGroundStateReg m α R bd) (Cexp : ℝ) : Prop where
  /-- `eq:Psi-H1`: `‖Ψ_R − ω_m^{-1/2}‖²_{H¹(B_m(1))} ≤ Cexp² R²`. -/
  psiH1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gsr.psi y - (Real.sqrt (omega m))⁻¹) ^ 2)
      + (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ‖Weak.classicalGrad (transLift m R gsr.psi) y‖ ^ 2) ≤ Cexp ^ 2 * R ^ 2
  /-- `eq:d-R`, first half: `|d_R − √ω_m| ≤ Cexp R`. -/
  dR_close : |(∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
      - Real.sqrt (omega m)| ≤ Cexp * R
  /-- `eq:d-R`, second half: `d_R ≥ √ω_m / 2`. -/
  dR_ge : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y
  /-- `eq:nu-expansion`: `|R² ν_R − m α R| ≤ Cexp R²`. -/
  nuExp : |R ^ 2 * gsr.nu - (m : ℝ) * α * R| ≤ Cexp * R ^ 2
  /-- The ground state's boundary form is the sphere integral of its continuous
  representative. -/
  bdSphere : bd gsr.psi gsr.psi = sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2)

/-! ## 7. The arc length of a cap profile -/

/-- The arc length `∫_{-K}^0 √(1 + θ'²) ds` of the cap profile.  It is finite because `θ` is
concave, hence `deriv θ` is integrable (`Cap.Concave.deriv_integrableOn`). -/
def capArcLength (C : Cap m) : ℝ :=
  ∫ s in Ioo (-C.K) 0, Real.sqrt (1 + deriv C.θ s ^ 2)

theorem integrableOn_capArc (C : Cap m) :
    IntegrableOn (fun s => Real.sqrt (1 + deriv C.θ s ^ 2)) (Ioo (-C.K) 0) := by
  have hd : IntegrableOn (deriv C.θ) (Ioo (-C.K) 0) := Cap.Concave.deriv_integrableOn C
  have hconst : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (-C.K) 0) := by
    refine integrableOn_const (hs := ?_) (hC := ?_)
    · exact (measure_Ioo_lt_top).ne
    · simp
  have hg : IntegrableOn (fun s => 1 + |deriv C.θ s|) (Ioo (-C.K) 0) := hconst.add hd.abs
  refine Integrable.mono' hg ?_ ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.add (hd.aestronglyMeasurable.pow 2)))
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : 1 + deriv C.θ s ^ 2 ≤ (1 + |deriv C.θ s|) ^ 2 := by
      nlinarith [abs_nonneg (deriv C.θ s), sq_abs (deriv C.θ s)]
    calc Real.sqrt (1 + deriv C.θ s ^ 2) ≤ Real.sqrt ((1 + |deriv C.θ s|) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = 1 + |deriv C.θ s| := Real.sqrt_sq (by positivity)

theorem capArcLength_nonneg (C : Cap m) : 0 ≤ capArcLength C :=
  setIntegral_nonneg measurableSet_Ioo fun _ _ => Real.sqrt_nonneg _

/-- `capAreaElement ≤ √(1+θ'²)` on `(-K, 0)` (because `0 < θ ≤ 1` there). -/
theorem capAreaElement_le_arc (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    capAreaElement C s ≤ Real.sqrt (1 + deriv C.θ s ^ 2) := by
  have h1 : C.θ s ^ (m - 1) ≤ 1 :=
    pow_le_one₀ (C.θ_pos s hs).le (C.θ_le_one s hs)
  have h2 : (0:ℝ) ≤ Real.sqrt (1 + deriv C.θ s ^ 2) := Real.sqrt_nonneg _
  calc capAreaElement C s = C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2) := rfl
    _ ≤ 1 * Real.sqrt (1 + deriv C.θ s ^ 2) := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

theorem capAreaElement_nonneg (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    0 ≤ capAreaElement C s :=
  mul_nonneg (pow_nonneg (C.θ_pos s hs).le _) (Real.sqrt_nonneg _)

/-! ## 8. Integrals of transverse functions over the cap body -/

theorem measurableSet_capBody (C : Cap m) : MeasurableSet C.body :=
  C.measurableSet_body (Cap.Concave.continuousOn_Ioo C)

theorem body_subset_cyl (C : Cap m) :
    C.body ⊆ Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  rintro p ⟨h1, h2, h3⟩
  exact ⟨⟨h1, h2⟩, by rw [mem_ball_zero_iff]; exact lt_of_lt_of_le h3 (C.θ_le_one p.1 ⟨h1, h2⟩)⟩

theorem integrableOn_snd_cyl (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) :
    IntegrableOn (fun p : CapSpace m => f p.2)
      (Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  have hc : IsCompact (Icc (-C.K) 0 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (isCompact_Icc).prod (isCompact_closedBall _ _)
  refine ((hf.comp continuous_snd).continuousOn.integrableOn_compact hc).mono_set ?_
  exact Set.prod_mono Ioo_subset_Icc_self ball_subset_closedBall

theorem integral_Ioo_one (C : Cap m) : (∫ _x in Ioo (-C.K) 0, (1:ℝ)) = C.K := by
  have hvol : (volume (Ioo (-C.K) 0)).toReal = C.K := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [C.hK])]
    ring
  rw [setIntegral_const, measureReal_def, hvol, smul_eq_mul, mul_one]

theorem setIntegral_cyl_snd (C : Cap m) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ p in Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, f p.2)
      = C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f y := by
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin m))))
      (fun _ : ℝ => (1:ℝ)) f (Ioo (-C.K) 0) (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
  simp only [one_mul] at h
  rw [← Measure.volume_eq_prod] at h
  rw [h, integral_Ioo_one]

/-- **The cap sits in the unit cylinder** (`eq:lift`): for a nonnegative continuous transverse
function, `∫_𝒞 f(z) ≤ K ∫_{B_m(1)} f`. -/
theorem setIntegral_body_le (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) :
    (∫ p in C.body, f p.2) ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f y := by
  have h1 : (∫ p in C.body, f p.2)
      ≤ ∫ p in Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, f p.2 :=
    setIntegral_mono_set (integrableOn_snd_cyl C hf)
      (Filter.Eventually.of_forall fun p => hf0 _) (body_subset_cyl C).eventuallyLE
  rwa [setIntegral_cyl_snd C f] at h1

theorem integrableOn_body_snd (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) : IntegrableOn (fun p : CapSpace m => f p.2) C.body :=
  (integrableOn_snd_cyl C hf).mono_set (body_subset_cyl C)

/-- The absolute-value form of `setIntegral_body_le`. -/
theorem abs_setIntegral_body_le (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) :
    |∫ p in C.body, f p.2| ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |f y| := by
  have h0 : |∫ p in C.body, f p.2| ≤ ∫ p in C.body, |f p.2| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict C.body)
        (f := fun p : CapSpace m => f p.2)
  exact h0.trans (setIntegral_body_le C hf.abs fun y => abs_nonneg _)

theorem classicalGrad_sub_const {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Weak.classicalGrad (fun y => u y - c) x = Weak.classicalGrad u x := by
  ext i
  rw [Weak.classicalGrad_apply, Weak.classicalGrad_apply, fderiv_sub_const]

/-! ## 9. Integrability and linearity of the unit cap's lateral boundary integral -/

theorem integrable_sphere_comp (m : ℕ) (r t : ℝ) {G : CapSpace m → ℝ} (hG : Continuous G) :
    Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      G (t, r • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m) := by
  have hc : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      G (t, r • (ω : EuclideanSpace ℝ (Fin m)))) :=
    hG.comp (continuous_const.prodMk (continuous_const.smul continuous_subtype_val))
  have h := hc.continuousOn.integrableOn_compact (μ := sphereMeasure m) isCompact_univ
  rwa [integrableOn_univ] at h

theorem integrableOn_capAreaElement (C : Cap m) :
    IntegrableOn (capAreaElement C) (Ioo (-C.K) 0) := by
  have h := Cap.Concave.areaElement_intervalIntegrable C
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [C.hK])] at h
  exact h

/-- **The lateral density of a continuous integrand is integrable on the unit cap.** -/
theorem integrableOn_capLateralDensity (C : Cap m) {G : CapSpace m → ℝ} (hG : Continuous G) :
    IntegrableOn (capLateralDensity C G) (Ioo (-C.K) 0) := by
  classical
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    ((isCompact_Icc (a := -C.K) (b := (0:ℝ))).prod
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) hG.continuousOn
  set M' : ℝ := max M 0 with hM'
  have hM'0 : (0:ℝ) ≤ M' := le_max_right _ _
  set σtot : ℝ := ((sphereMeasure m) univ).toReal with hσ
  have hσ0 : (0:ℝ) ≤ σtot := ENNReal.toReal_nonneg
  -- the spherical average is a.e. strongly measurable
  have hθ : AEMeasurable C.θ (volume.restrict (Ioo (-C.K) 0)) :=
    (Cap.Concave.continuousOn_Ioo C).aemeasurable measurableSet_Ioo
  obtain ⟨pθ, hpm, hae⟩ := hθ
  have hmap : Measurable fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ((q.1 : ℝ), pθ q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) :=
    measurable_fst.prodMk ((hpm.comp measurable_fst).smul
      (measurable_subtype_coe.comp measurable_snd))
  have hF : StronglyMeasurable fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      G (q.1, pθ q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) :=
    (hG.measurable.comp hmap).stronglyMeasurable
  have h1 : StronglyMeasurable fun s : ℝ =>
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        G (s, pθ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) :=
    hF.integral_prod_right' (ν := sphereMeasure m)
  have hS : AEStronglyMeasurable (fun s => ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      G (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (volume.restrict (Ioo (-C.K) 0)) := by
    refine h1.aestronglyMeasurable.congr (hae.mono fun s hs => ?_)
    simp only [hs]
  have hA : IntegrableOn (capAreaElement C) (Ioo (-C.K) 0) := integrableOn_capAreaElement C
  refine Integrable.mono' (g := fun s => M' * σtot * |capAreaElement C s|)
    (hA.abs.const_mul _) (hA.aestronglyMeasurable.mul hS) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hmem : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      ((s : ℝ), C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        ∈ Icc (-C.K) (0:ℝ) ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro ω
    refine ⟨⟨hs.1.le, hs.2.le⟩, ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (C.θ_pos s hs), mem_sphere_zero_iff_norm.1 ω.2, mul_one]
    exact C.θ_le_one s hs
  have havg : |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      G (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)| ≤ M' * σtot := by
    have h := norm_integral_le_of_norm_le_const (μ := sphereMeasure m)
      (f := fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        G (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))) (C := M')
      (Filter.Eventually.of_forall fun ω => (hM _ (hmem ω)).trans (le_max_left _ _))
    simpa only [Real.norm_eq_abs, measureReal_def] using h
  show ‖capAreaElement C s * _‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  calc |capAreaElement C s| * |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        G (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)|
      ≤ |capAreaElement C s| * (M' * σtot) :=
        mul_le_mul_of_nonneg_left havg (abs_nonneg _)
    _ = M' * σtot * |capAreaElement C s| := by ring

theorem capLateralDensity_sub (C : Cap m) {G H : CapSpace m → ℝ} (hG : Continuous G)
    (hH : Continuous H) (s : ℝ) :
    capLateralDensity C (fun p => G p - H p) s
      = capLateralDensity C G s - capLateralDensity C H s := by
  rw [capLateralDensity, capLateralDensity, capLateralDensity,
    integral_sub (integrable_sphere_comp m (C.θ s) s hG) (integrable_sphere_comp m (C.θ s) s hH)]
  ring

theorem capLateralIntegral_sub (C : Cap m) {G H : CapSpace m → ℝ} (hG : Continuous G)
    (hH : Continuous H) :
    capLateralIntegral C (fun p => G p - H p)
      = capLateralIntegral C G - capLateralIntegral C H := by
  rw [capLateralIntegral, capLateralIntegral, capLateralIntegral,
    ← integral_sub (integrableOn_capLateralDensity C hG) (integrableOn_capLateralDensity C hH)]
  exact setIntegral_congr_fun measurableSet_Ioo fun s _ => capLateralDensity_sub C hG hH s

theorem capLateralIntegral_const (C : Cap m) (hm : 1 ≤ m) (a : ℝ) :
    capLateralIntegral C (fun _ => a) = a * C.lateralArea := by
  have h0 : (-C.K : ℝ) ≤ 0 := by linarith [C.hK]
  have hpt : ∀ s : ℝ, capLateralDensity C (fun _ => a) s
      = a * ((m : ℝ) * omega m) * capAreaElement C s := by
    intro s
    rw [capLateralDensity, integral_const, measureReal_def, sphere_measure_univ m hm,
      smul_eq_mul]
    ring
  rw [capLateralIntegral, setIntegral_congr_fun measurableSet_Ioo (fun s _ => hpt s),
    integral_const_mul, RobinCaps.ThinDomain.lateralArea_eq C,
    intervalIntegral_eq_integral_Ioo h0]
  ring

/-! ## 10. Elementary quantitative inequalities -/

/-- `|x² − c²| ≤ (1 + c/R)(x − c)² + cR` (Young's inequality with parameter `R`). -/
theorem abs_sq_sub_sq_le {x c R : ℝ} (hc : 0 ≤ c) (hR : 0 < R) :
    |x ^ 2 - c ^ 2| ≤ (1 + c / R) * (x - c) ^ 2 + c * R := by
  have he : x ^ 2 - c ^ 2 = (x - c) ^ 2 + 2 * c * (x - c) := by ring
  have hh : |x ^ 2 - c ^ 2| ≤ (x - c) ^ 2 + 2 * c * |x - c| := by
    rw [he]
    calc |(x - c) ^ 2 + 2 * c * (x - c)| ≤ |(x - c) ^ 2| + |2 * c * (x - c)| := abs_add_le _ _
      _ = (x - c) ^ 2 + 2 * c * |x - c| := by
          rw [abs_of_nonneg (sq_nonneg _), abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * c)]
  have h2 : 2 * |x - c| ≤ (x - c) ^ 2 / R + R := by
    have hsq : |x - c| ^ 2 = (x - c) ^ 2 := sq_abs _
    have hnn := sq_nonneg (|x - c| - R)
    rw [div_add' _ _ _ hR.ne', le_div_iff₀ hR]
    nlinarith [hnn, hsq]
  have h3 : 2 * c * |x - c| ≤ c / R * (x - c) ^ 2 + c * R := by
    have := mul_le_mul_of_nonneg_left h2 hc
    have he2 : c * ((x - c) ^ 2 / R + R) = c / R * (x - c) ^ 2 + c * R := by
      field_simp
    nlinarith [this, he2]
  nlinarith [hh, h3]

theorem sqrt_omega_pos (m : ℕ) : 0 < Real.sqrt (omega m) :=
  Real.sqrt_pos.2 (Cap.omega_pos m)

theorem inv_sqrt_omega_sq (m : ℕ) : ((Real.sqrt (omega m))⁻¹) ^ 2 = (omega m)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Cap.omega_pos m).le]

theorem integrableOn_ball_one_of_continuous {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).mono_set ball_subset_closedBall

theorem integrableOn_ball_of_continuous {f : EuclideanSpace ℝ (Fin m) → ℝ} {r : ℝ}
    (hf : Continuous f) : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) r) :=
  (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) r)).mono_set ball_subset_closedBall

theorem integral_ball_one (m : ℕ) (hm : 1 ≤ m) :
    (∫ _y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (1:ℝ)) = omega m := by
  rw [setIntegral_const, measureReal_def, volume_ball_toReal m hm zero_le_one, smul_eq_mul,
    mul_one, one_pow, one_mul]

/-! ## 11. The two basic quadratic comparisons for `Ψ_R` -/

/-- On any ball of radius `r ≤ 1`: `∫ |Ψ² − c²| ≤ (1 + c/R)∫(Ψ−c)² + cR·|B_r|`. -/
theorem integral_abs_sq_sub_le (m : ℕ) (hm : 1 ≤ m) {Ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hΨ : Continuous Ψ) {c R r : ℝ} (hc : 0 ≤ c) (hR : 0 < R) (hr : 0 ≤ r) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) r, |Ψ y ^ 2 - c ^ 2|)
      ≤ (1 + c / R) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) r, (Ψ y - c) ^ 2)
        + c * R * (r ^ m * omega m) := by
  have h1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) r, |Ψ y ^ 2 - c ^ 2|)
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) r,
          ((1 + c / R) * (Ψ y - c) ^ 2 + c * R) := by
    refine setIntegral_mono_on
      (integrableOn_ball_of_continuous ((hΨ.pow 2).sub continuous_const).abs)
      (integrableOn_ball_of_continuous
        ((continuous_const.mul ((hΨ.sub continuous_const).pow 2)).add continuous_const))
      measurableSet_ball fun y _ => abs_sq_sub_sq_le hc hR
  have h2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) r,
      ((1 + c / R) * (Ψ y - c) ^ 2 + c * R))
      = (1 + c / R) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) r, (Ψ y - c) ^ 2)
        + c * R * (r ^ m * omega m) := by
    rw [integral_add (integrableOn_ball_of_continuous
        (continuous_const.mul ((hΨ.sub continuous_const).pow 2)))
      (integrableOn_ball_of_continuous continuous_const),
      integral_const_mul, setIntegral_const, measureReal_def,
      volume_ball_toReal m hm hr, smul_eq_mul]
    ring
  linarith [h1, h2]

/-- The same comparison on the sphere of radius `ρ`. -/
theorem sphere_abs_sq_sub_le (m : ℕ) (hm : 1 ≤ m) {Ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hΨ : Continuous Ψ) {c R ρ : ℝ} (hc : 0 ≤ c) (hR : 0 < R) :
    |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2) ∂(sphereMeasure m)|
      ≤ (1 + c / R) * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2 ∂(sphereMeasure m))
          + c * R * ((m : ℝ) * omega m) := by
  have hint1 : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2) (sphereMeasure m) :=
    integrable_sphere_comp m ρ 0 (((hΨ.comp continuous_snd).pow 2).sub continuous_const)
  have hint2 : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2) (sphereMeasure m) :=
    integrable_sphere_comp m ρ 0 (((hΨ.comp continuous_snd).sub continuous_const).pow 2)
  have hint3 : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (1 + c / R) * (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2 + c * R)
      (sphereMeasure m) := (hint2.const_mul _).add (integrable_const _)
  have h0 : |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2) ∂(sphereMeasure m)|
      ≤ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          |Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2| ∂(sphereMeasure m) := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := sphereMeasure m)
        (f := fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2)
  have h1 : (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2| ∂(sphereMeasure m))
      ≤ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          ((1 + c / R) * (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2 + c * R)
          ∂(sphereMeasure m) :=
    integral_mono hint1.abs hint3 (fun ω => abs_sq_sub_sq_le hc hR)
  have h2 : (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      ((1 + c / R) * (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2 + c * R)
      ∂(sphereMeasure m))
      = (1 + c / R) * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            (Ψ (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2 ∂(sphereMeasure m))
          + c * R * ((m : ℝ) * omega m) := by
    rw [integral_add (hint2.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, measureReal_def, sphere_measure_univ m hm, smul_eq_mul]
    ring
  linarith [h0, h1, h2]

/-! ## 12. The cap estimates of `lem:cap-upper` -/

/-- `∫_Γ Φ² dℋ^m` over the *unit* cap's exposed boundary (lateral surface plus terminal disk),
for a function `Φ` of the transverse variable only. -/
def capJterm (C : Cap m) (Φ : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  capLateralIntegral C (fun p => Φ p.2 ^ 2)
    + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), Φ z ^ 2

theorem capJterm_const (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0) (a : ℝ) :
    capJterm C (fun _ => a) = a ^ 2 * C.revolutionArea := by
  rw [capJterm, capLateralIntegral_const C hm, setIntegral_const, measureReal_def,
    volume_ball_toReal m hm hθ0, smul_eq_mul, Cap.revolutionArea, Cap.terminalArea]
  ring

theorem integral_capAreaElement (C : Cap m) :
    (m : ℝ) * omega m * ∫ s in Ioo (-C.K) 0, capAreaElement C s = C.lateralArea := by
  rw [RobinCaps.ThinDomain.lateralArea_eq C,
    intervalIntegral_eq_integral_Ioo (by linarith [C.hK])]

section CapUpper

variable {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
  {gsr : TransverseGroundStateReg m α R bd} {Cexp : ℝ}

/-- The `H¹(B_m(1))` bound of `eq:Psi-H1`, split into its two halves. -/
theorem TransverseExpansionData.l2_le (hexp : TransverseExpansionData m α R gsr Cexp) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gsr.psi y - (Real.sqrt (omega m))⁻¹) ^ 2) ≤ Cexp ^ 2 * R ^ 2 := by
  have h2 : (0:ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ‖Weak.classicalGrad (transLift m R gsr.psi) y‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  linarith [hexp.psiH1]

theorem TransverseExpansionData.grad_le (hexp : TransverseExpansionData m α R gsr Cexp) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ‖Weak.classicalGrad (transLift m R gsr.psi) y‖ ^ 2) ≤ Cexp ^ 2 * R ^ 2 := by
  have h2 : (0:ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gsr.psi y - (Real.sqrt (omega m))⁻¹) ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
  linarith [hexp.psiH1]

/-- **`eq:upper-gradient`**: `∫_𝒞 |∇_zΨ_R|² ≤ K C² R²`, hence `R⁻¹∫_𝒞|∇_zΨ_R|² ≤ K C² R`. -/
theorem cap_upper_gradient (C : Cap m) (hexp : TransverseExpansionData m α R gsr Cexp) :
    (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2) ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
  have hΨ : ContDiff ℝ 1 (transLift m R gsr.psi) := contDiff_transLift gsr.psiC1
  have hrw : (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
      = ∫ p in C.body, ‖Weak.classicalGrad (transLift m R gsr.psi) p.2‖ ^ 2 :=
    setIntegral_congr_fun (measurableSet_capBody C)
      fun p _ => by rw [gradZP_capGroundLift gsr.psiC1]
  rw [hrw]
  refine (setIntegral_body_le C ((Weak.continuous_classicalGrad _ hΨ).norm.pow 2)
    (fun y => by positivity)).trans ?_
  exact mul_le_mul_of_nonneg_left hexp.grad_le C.hK.le

/-- **`eq:upper-mass`**, crude form: `∫_𝒞 Ψ_R² ≤ K`, hence `R‖Ψ_R‖²_{L²(𝒞)} ≤ K R`. -/
theorem cap_mass_le (hR : 0 < R) (C : Cap m) (gsr : TransverseGroundStateReg m α R bd) :
    (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2) ≤ C.K := by
  have hΨc : Continuous (transLift m R gsr.psi) := (contDiff_transLift gsr.psiC1).continuous
  have h := setIntegral_body_le C (f := fun y => transLift m R gsr.psi y ^ 2)
    (hΨc.pow 2) (fun y => sq_nonneg _)
  rw [integral_transLift_sq hR gsr, mul_one] at h
  exact h

theorem cap_mass_nonneg (C : Cap m) (gsr : TransverseGroundStateReg m α R bd) :
    0 ≤ ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2 :=
  setIntegral_nonneg (measurableSet_capBody C) fun _ _ => sq_nonneg _

/-- **`eq:upper-mass`**, sharp form: `∫_𝒞 Ψ_R² = |𝒞|/ω_m + O(R)`. -/
theorem cap_mass_expansion (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1) (C : Cap m)
    (hexp : TransverseExpansionData m α R gsr Cexp) :
    |(∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
        - (omega m)⁻¹ * C.revolutionVolume|
      ≤ C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
          + (Real.sqrt (omega m))⁻¹ * omega m) * R := by
  set c : ℝ := (Real.sqrt (omega m))⁻¹ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (inv_pos.2 (sqrt_omega_pos m))
  have hΨc : Continuous (transLift m R gsr.psi) := (contDiff_transLift gsr.psiC1).continuous
  have hc2 : c ^ 2 = (omega m)⁻¹ := by rw [hcdef]; exact inv_sqrt_omega_sq m
  have hvol : (volume C.body).toReal = C.revolutionVolume := Cap.volume_body_eq_of_cap m C
  have hcg : (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
      = ∫ p in C.body, transLift m R gsr.psi p.2 ^ 2 := rfl
  have hs1 : (∫ p in C.body, (transLift m R gsr.psi p.2 ^ 2 - c ^ 2))
      = (∫ p in C.body, transLift m R gsr.psi p.2 ^ 2)
        - (omega m)⁻¹ * C.revolutionVolume := by
    rw [integral_sub (integrableOn_body_snd C (hΨc.pow 2))
      (integrableOn_body_snd C (f := fun _ : EuclideanSpace ℝ (Fin m) => c ^ 2)
        continuous_const),
      setIntegral_const, measureReal_def, smul_eq_mul, hvol, hc2]
    ring
  have hs2 : |∫ p in C.body, (transLift m R gsr.psi p.2 ^ 2 - c ^ 2)|
      ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          |transLift m R gsr.psi y ^ 2 - c ^ 2| :=
    abs_setIntegral_body_le C ((hΨc.pow 2).sub continuous_const)
  have hs3 := integral_abs_sq_sub_le m hm hΨc (c := c) (R := R) (r := 1) hc0 hR zero_le_one
  rw [one_pow, one_mul] at hs3
  have hs4 := hexp.l2_le
  rw [← hcdef] at hs4
  have hpos : (0:ℝ) ≤ 1 + c / R := by positivity
  have hA : (1 + c / R) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gsr.psi y - c) ^ 2) ≤ (1 + c / R) * (Cexp ^ 2 * R ^ 2) :=
    mul_le_mul_of_nonneg_left hs4 hpos
  have hB : (1 + c / R) * (Cexp ^ 2 * R ^ 2) = Cexp ^ 2 * R ^ 2 + c * Cexp ^ 2 * R := by
    field_simp
  have hR2 : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
  have hR2mul : Cexp ^ 2 * R ^ 2 ≤ Cexp ^ 2 * R :=
    mul_le_mul_of_nonneg_left hR2 (sq_nonneg _)
  have hcomb : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      |transLift m R gsr.psi y ^ 2 - c ^ 2|)
      ≤ (Cexp ^ 2 + c * Cexp ^ 2 + c * omega m) * R := by
    nlinarith [hs3, hA, hB, hR2mul]
  rw [hcg, ← hs1]
  calc |∫ p in C.body, (transLift m R gsr.psi p.2 ^ 2 - c ^ 2)|
      ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          |transLift m R gsr.psi y ^ 2 - c ^ 2| := hs2
    _ ≤ C.K * ((Cexp ^ 2 + c * Cexp ^ 2 + c * omega m) * R) :=
        mul_le_mul_of_nonneg_left hcomb C.hK.le
    _ = C.K * (Cexp ^ 2 + c * Cexp ^ 2 + c * omega m) * R := by ring

set_option maxHeartbeats 2000000 in
/-- **`eq:upper-J`**, the boundary part: `∫_Γ Ψ_R² dℋ^m = ℋ^m(Γ)/ω_m + O(R)`.

This is where the radial trace inequality `ball_trace_ineq_c1` enters. -/
theorem cap_boundary_expansion (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1) (C : Cap m)
    (hθ0 : 0 ≤ C.θ 0) (hθ1 : C.θ 0 ≤ 1)
    (hexp : TransverseExpansionData m α R gsr Cexp) :
    |capJterm C (transLift m R gsr.psi) - (omega m)⁻¹ * C.revolutionArea|
      ≤ (capArcLength C * (2 ^ (m + 1) * Cexp ^ 2 * (1 + (Real.sqrt (omega m))⁻¹))
          + (Real.sqrt (omega m))⁻¹ * C.lateralArea
          + (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
              + (Real.sqrt (omega m))⁻¹ * C.terminalArea)) * R := by
  set c : ℝ := (Real.sqrt (omega m))⁻¹ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (inv_pos.2 (sqrt_omega_pos m))
  have hΨ : ContDiff ℝ 1 (transLift m R gsr.psi) := contDiff_transLift gsr.psiC1
  have hΨc : Continuous (transLift m R gsr.psi) := hΨ.continuous
  have hc2 : c ^ 2 = (omega m)⁻¹ := by rw [hcdef]; exact inv_sqrt_omega_sq m
  have hH1 := hexp.psiH1
  rw [← hcdef] at hH1
  have hs4 := hexp.l2_le
  rw [← hcdef] at hs4
  have hR2 : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
  -- the uniform trace bound
  have htrace : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ρ ^ (m - 1) * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gsr.psi (ρ • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2
        ∂(sphereMeasure m)) ≤ 2 ^ (m + 1) * (Cexp ^ 2 * R ^ 2) := by
    intro ρ hρ hρ1
    have h := ball_trace_ineq_c1 m hm
      (g := fun y => transLift m R gsr.psi y - c)
      (hΨ.sub contDiff_const) hρ hρ1
    simp only [classicalGrad_sub_const] at h
    exact h.trans (mul_le_mul_of_nonneg_left hH1 (by positivity))
  -- the lateral piece
  set G : CapSpace m → ℝ := fun p => transLift m R gsr.psi p.2 ^ 2 - c ^ 2 with hGdef
  have hGc : Continuous G := by
    rw [hGdef]; exact ((hΨc.comp continuous_snd).pow 2).sub continuous_const
  set X : ℝ := (1 + c / R) * (2 ^ (m + 1) * (Cexp ^ 2 * R ^ 2)) with hXdef
  set Y : ℝ := c * R * ((m : ℝ) * omega m) with hYdef
  have hptw : ∀ s ∈ Ioo (-C.K) 0, |capLateralDensity C G s|
      ≤ X * Real.sqrt (1 + deriv C.θ s ^ 2) + Y * capAreaElement C s := by
    intro s hs
    have hθp : 0 < C.θ s := C.θ_pos s hs
    have hθle : C.θ s ≤ 1 := C.θ_le_one s hs
    have hae0 : 0 ≤ capAreaElement C s := capAreaElement_nonneg C hs
    have hsq0 : (0:ℝ) ≤ Real.sqrt (1 + deriv C.θ s ^ 2) := Real.sqrt_nonneg _
    have hsph := sphere_abs_sq_sub_le m hm hΨc (c := c) (R := R) (ρ := C.θ s) hc0 hR
    have htr := htrace (C.θ s) hθp hθle
    have hden : capLateralDensity C G s
        = capAreaElement C s * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            (transLift m R gsr.psi (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 - c ^ 2)
            ∂(sphereMeasure m) := by
      rw [capLateralDensity, hGdef]
    rw [hden, abs_mul, abs_of_nonneg hae0]
    have hstep1 := mul_le_mul_of_nonneg_left hsph hae0
    have hstep2 : capAreaElement C s
          * ((1 + c / R) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              (transLift m R gsr.psi (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2
              ∂(sphereMeasure m))
        = Real.sqrt (1 + deriv C.θ s ^ 2)
            * ((1 + c / R) * (C.θ s ^ (m - 1) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
                (transLift m R gsr.psi (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2
                ∂(sphereMeasure m))) := by
      rw [capAreaElement]; ring
    have hstep3 : (1 + c / R) * (C.θ s ^ (m - 1)
          * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            (transLift m R gsr.psi (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2
            ∂(sphereMeasure m))
        ≤ X := by
      rw [hXdef]
      exact mul_le_mul_of_nonneg_left htr (by positivity)
    have hstep4 : Real.sqrt (1 + deriv C.θ s ^ 2)
          * ((1 + c / R) * (C.θ s ^ (m - 1) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              (transLift m R gsr.psi (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) - c) ^ 2
              ∂(sphereMeasure m)))
        ≤ Real.sqrt (1 + deriv C.θ s ^ 2) * X :=
      mul_le_mul_of_nonneg_left hstep3 hsq0
    nlinarith [hstep1, hstep2, hstep4]
  have habsint : |capLateralIntegral C G|
      ≤ ∫ s in Ioo (-C.K) 0, |capLateralDensity C G s| := by
    simpa only [Real.norm_eq_abs, capLateralIntegral] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioo (-C.K) 0))
        (f := capLateralDensity C G)
  have hmono : (∫ s in Ioo (-C.K) 0, |capLateralDensity C G s|)
      ≤ ∫ s in Ioo (-C.K) 0,
          (X * Real.sqrt (1 + deriv C.θ s ^ 2) + Y * capAreaElement C s) :=
    setIntegral_mono_on ((integrableOn_capLateralDensity C hGc).abs)
      (((integrableOn_capArc C).const_mul X).add
        ((integrableOn_capAreaElement C).const_mul Y)) measurableSet_Ioo hptw
  have heval : (∫ s in Ioo (-C.K) 0,
        (X * Real.sqrt (1 + deriv C.θ s ^ 2) + Y * capAreaElement C s))
      = X * capArcLength C + Y * ∫ s in Ioo (-C.K) 0, capAreaElement C s := by
    rw [integral_add ((integrableOn_capArc C).const_mul X)
        ((integrableOn_capAreaElement C).const_mul Y),
      integral_const_mul, integral_const_mul, capArcLength]
  have hYA : Y * (∫ s in Ioo (-C.K) 0, capAreaElement C s) = c * R * C.lateralArea := by
    rw [hYdef, ← integral_capAreaElement C]; ring
  have hXval : X ≤ 2 ^ (m + 1) * Cexp ^ 2 * (1 + c) * R := by
    rw [hXdef]
    have he : (1 + c / R) * (2 ^ (m + 1) * (Cexp ^ 2 * R ^ 2))
        = 2 ^ (m + 1) * Cexp ^ 2 * (R ^ 2 + c * R) := by field_simp
    rw [he]
    have h1 : R ^ 2 + c * R ≤ (1 + c) * R := by nlinarith [hR2, hc0]
    have h2 : (0:ℝ) ≤ 2 ^ (m + 1) * Cexp ^ 2 := by positivity
    nlinarith [h1, h2]
  have hlatfin : |capLateralIntegral C G|
      ≤ capArcLength C * (2 ^ (m + 1) * Cexp ^ 2 * (1 + c)) * R + c * R * C.lateralArea := by
    have hΛ0 : 0 ≤ capArcLength C := capArcLength_nonneg C
    have h1 : X * capArcLength C
        ≤ (2 ^ (m + 1) * Cexp ^ 2 * (1 + c) * R) * capArcLength C :=
      mul_le_mul_of_nonneg_right hXval hΛ0
    linarith [habsint, hmono, heval, hYA, h1]
  have hlatsub : capLateralIntegral C (fun p => transLift m R gsr.psi p.2 ^ 2)
      - c ^ 2 * C.lateralArea = capLateralIntegral C G := by
    have h := capLateralIntegral_sub C
      (G := fun p : CapSpace m => transLift m R gsr.psi p.2 ^ 2)
      (H := fun _ : CapSpace m => c ^ 2)
      ((hΨc.comp continuous_snd).pow 2) continuous_const
    rw [capLateralIntegral_const C hm] at h
    rw [hGdef, ← h]
  -- the terminal disk
  have hdisksub : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
        transLift m R gsr.psi z ^ 2) - c ^ 2 * C.terminalArea
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
          (transLift m R gsr.psi z ^ 2 - c ^ 2) := by
    rw [integral_sub (integrableOn_ball_of_continuous (hΨc.pow 2))
        (integrableOn_ball_of_continuous continuous_const),
      setIntegral_const, measureReal_def, volume_ball_toReal m hm hθ0, smul_eq_mul,
      Cap.terminalArea]
    ring
  have hdiskabs : |∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
        (transLift m R gsr.psi z ^ 2 - c ^ 2)|
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
          |transLift m R gsr.psi z ^ 2 - c ^ 2| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0)))
        (f := fun z => transLift m R gsr.psi z ^ 2 - c ^ 2)
  have hdisk3 := integral_abs_sq_sub_le m hm hΨc (c := c) (R := R) (r := C.θ 0) hc0 hR hθ0
  have hdisk4 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
        (transLift m R gsr.psi z - c) ^ 2)
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (transLift m R gsr.psi z - c) ^ 2 :=
    setIntegral_mono_set
      (integrableOn_ball_one_of_continuous ((hΨc.sub continuous_const).pow 2))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (ball_subset_ball hθ1).eventuallyLE
  have hdiskfin : |(∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
        transLift m R gsr.psi z ^ 2) - c ^ 2 * C.terminalArea|
      ≤ (Cexp ^ 2 + c * Cexp ^ 2 + c * C.terminalArea) * R := by
    rw [hdisksub]
    have hpos : (0:ℝ) ≤ 1 + c / R := by positivity
    have hA : (1 + c / R) * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
        (transLift m R gsr.psi z - c) ^ 2) ≤ (1 + c / R) * (Cexp ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left (hdisk4.trans hs4) hpos
    have hB : (1 + c / R) * (Cexp ^ 2 * R ^ 2) = Cexp ^ 2 * R ^ 2 + c * Cexp ^ 2 * R := by
      field_simp
    have hR2mul : Cexp ^ 2 * R ^ 2 ≤ Cexp ^ 2 * R :=
      mul_le_mul_of_nonneg_left hR2 (sq_nonneg _)
    have hTA : c * R * (C.θ 0 ^ m * omega m) = c * R * C.terminalArea := by
      rw [Cap.terminalArea]; ring
    nlinarith [hdiskabs, hdisk3, hA, hB, hR2mul, hTA]
  -- assemble
  have hsplit : capJterm C (transLift m R gsr.psi) - (omega m)⁻¹ * C.revolutionArea
      = capLateralIntegral C G
        + ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
            transLift m R gsr.psi z ^ 2) - c ^ 2 * C.terminalArea) := by
    rw [capJterm, ← hlatsub, Cap.revolutionArea, ← hc2]
    ring
  rw [hsplit]
  calc |capLateralIntegral C G
        + ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
            transLift m R gsr.psi z ^ 2) - c ^ 2 * C.terminalArea)|
      ≤ |capLateralIntegral C G|
        + |(∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
            transLift m R gsr.psi z ^ 2) - c ^ 2 * C.terminalArea| := abs_add_le _ _
    _ ≤ (capArcLength C * (2 ^ (m + 1) * Cexp ^ 2 * (1 + c)) * R + c * R * C.lateralArea)
        + (Cexp ^ 2 + c * Cexp ^ 2 + c * C.terminalArea) * R :=
          add_le_add hlatfin hdiskfin
    _ = (capArcLength C * (2 ^ (m + 1) * Cexp ^ 2 * (1 + c)) + c * C.lateralArea
        + (Cexp ^ 2 + c * Cexp ^ 2 + c * C.terminalArea)) * R := by ring

/-! ## 13. The `J`-form of `eq:J-definition` and the full `eq:upper-J` -/

/-- `J[U] = α ∫_Γ |U|² dℋ^m − mα ∫_𝒞 |U|²` (`eq:J-definition`) for the unit cap. -/
def capJForm (m : ℕ) (α : ℝ) (C : Cap m) (Φ : CapSpace m → ℝ) : ℝ :=
  α * (capLateralIntegral C (fun p => Φ p ^ 2)
      + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), Φ (0, z) ^ 2)
    - (m : ℝ) * α * ∫ p in C.body, Φ p ^ 2

/-- The explicit constant of `cap_mass_expansion`. -/
def capMassConst (m : ℕ) (C : Cap m) (Cexp : ℝ) : ℝ :=
  C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * omega m)

/-- The explicit constant of `cap_boundary_expansion`. -/
def capBdryConst (m : ℕ) (C : Cap m) (Cexp : ℝ) : ℝ :=
  capArcLength C * (2 ^ (m + 1) * Cexp ^ 2 * (1 + (Real.sqrt (omega m))⁻¹))
    + (Real.sqrt (omega m))⁻¹ * C.lateralArea
    + (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
        + (Real.sqrt (omega m))⁻¹ * C.terminalArea)

theorem capJForm_capGroundLift (α : ℝ) (C : Cap m)
    (gsr : TransverseGroundStateReg m α R bd) :
    capJForm m α C (capGroundLift m R gsr.psi)
      = α * capJterm C (transLift m R gsr.psi)
        - (m : ℝ) * α * ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2 := rfl

/-- `|δ_R| = |R ν_R − m α| ≤ Cexp R` (`eq:nu-expansion`). -/
theorem abs_delta_le (hR : 0 < R) (hexp : TransverseExpansionData m α R gsr Cexp) :
    |R * gsr.nu - (m : ℝ) * α| ≤ Cexp * R := by
  have h := hexp.nuExp
  have he : R ^ 2 * gsr.nu - (m : ℝ) * α * R = R * (R * gsr.nu - (m : ℝ) * α) := by ring
  rw [he, abs_mul, abs_of_pos hR] at h
  have h3 : R * |R * gsr.nu - (m : ℝ) * α| ≤ R * (Cexp * R) := by nlinarith [h]
  exact le_of_mul_le_mul_left h3 hR

/-- **`eq:upper-J`**: `J[Ψ_R] − δ_R‖Ψ_R‖²_{L²(𝒞)} = β(𝒞) + O(R)`. -/
theorem cap_upper_J (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1) (C : Cap m)
    (hθ0 : 0 ≤ C.θ 0) (hθ1 : C.θ 0 ≤ 1)
    (hexp : TransverseExpansionData m α R gsr Cexp) :
    |capJForm m α C (capGroundLift m R gsr.psi)
        - (R * gsr.nu - (m : ℝ) * α) * (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
        - Cap.beta C α|
      ≤ (|α| * capBdryConst m C Cexp + (m : ℝ) * |α| * capMassConst m C Cexp
          + Cexp * C.K) * R := by
  have hJ := cap_boundary_expansion hm hR hR1 C hθ0 hθ1 hexp
  have hM := cap_mass_expansion hm hR hR1 C hexp
  have hMle := cap_mass_le hR C gsr
  have hM0 := cap_mass_nonneg C gsr
  have hδ := abs_delta_le hR hexp
  have hbeta : Cap.beta C α
      = α * ((omega m)⁻¹ * C.revolutionArea)
        - (m : ℝ) * α * ((omega m)⁻¹ * C.revolutionVolume) := by
    rw [Cap.beta, Cap.F, Cap.revolutionF]
    field_simp
  set MM : ℝ := ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2 with hMM
  set JJ : ℝ := capJterm C (transLift m R gsr.psi) with hJJ
  have hsplit : capJForm m α C (capGroundLift m R gsr.psi)
      - (R * gsr.nu - (m : ℝ) * α) * MM - Cap.beta C α
      = α * (JJ - (omega m)⁻¹ * C.revolutionArea)
        - (m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume)
        - (R * gsr.nu - (m : ℝ) * α) * MM := by
    rw [capJForm_capGroundLift, hbeta]
    ring
  rw [hsplit]
  have h1 : |α * (JJ - (omega m)⁻¹ * C.revolutionArea)|
      ≤ |α| * (capBdryConst m C Cexp * R) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hJ (abs_nonneg _)
  have h2 : |(m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume)|
      ≤ (m : ℝ) * |α| * (capMassConst m C Cexp * R) := by
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have := mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ) ≤ (m : ℝ) * |α|)
    calc (m : ℝ) * |α| * |MM - (omega m)⁻¹ * C.revolutionVolume|
        ≤ (m : ℝ) * |α| * (C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
            + (Real.sqrt (omega m))⁻¹ * omega m) * R) := this
      _ = (m : ℝ) * |α| * (capMassConst m C Cexp * R) := by rw [capMassConst]
  have h3 : |(R * gsr.nu - (m : ℝ) * α) * MM| ≤ Cexp * C.K * R := by
    rw [abs_mul, abs_of_nonneg hM0]
    calc |R * gsr.nu - (m : ℝ) * α| * MM ≤ (Cexp * R) * MM :=
          mul_le_mul_of_nonneg_right hδ hM0
      _ ≤ (Cexp * R) * C.K :=
          mul_le_mul_of_nonneg_left hMle (le_trans (abs_nonneg _) hδ)
      _ = Cexp * C.K * R := by ring
  have tri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    rw [sub_eq_add_neg]
    calc |x + -y| ≤ |x| + |-y| := abs_add_le _ _
      _ = |x| + |y| := by rw [abs_neg]
  have t1 := tri (α * (JJ - (omega m)⁻¹ * C.revolutionArea)
      - (m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume))
      ((R * gsr.nu - (m : ℝ) * α) * MM)
  have t2 := tri (α * (JJ - (omega m)⁻¹ * C.revolutionArea))
      ((m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume))
  linarith [t1, t2, h1, h2, h3]

end CapUpper

/-! ## 14. The uniform hypothesis and the three targets of `lem:cap-upper` -/

/-- **The uniform form of `lem:transverse`**: one constant `Cexp` serves all small `R` and
every ground state, and `ν_R` depends on `R` only. -/
def UniformTransverseExpansion (m : ℕ) (α : ℝ) : Prop :=
  ∃ (Cexp R₀ : ℝ) (nu : ℝ → ℝ), 0 < R₀ ∧ R₀ ≤ 1 ∧
    ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
        (gsr : TransverseGroundStateReg m α R bd),
        TransverseExpansionData m α R gsr Cexp ∧ gsr.nu = nu R

/-- **`eq:upper-gradient` of `lem:cap-upper`**, as the target of `Trial.lean`. -/
theorem capUpperGradientTarget (m : ℕ) (α : ℝ) (C : Cap m)
    (h : UniformTransverseExpansion m α) : CapUpperGradientTarget m α C := by
  obtain ⟨Cexp, R₀, nu, hR₀, hR₀1, hh⟩ := h
  refine ⟨C.K * Cexp ^ 2, R₀, hR₀, fun R hR hRlt bd gsr => ?_⟩
  obtain ⟨hexp, -⟩ := hh R hR hRlt bd gsr
  have hg := cap_upper_gradient C hexp
  have hnn : (0:ℝ) ≤ ∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_capBody C) fun _ _ => by positivity
  have hRinv : (0:ℝ) ≤ R⁻¹ := by positivity
  rw [abs_of_nonneg (mul_nonneg hRinv hnn)]
  calc R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
      ≤ R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) := mul_le_mul_of_nonneg_left hg hRinv
    _ = C.K * Cexp ^ 2 * R := by field_simp

/-- **`eq:upper-mass` of `lem:cap-upper`**, as the target of `Trial.lean`. -/
theorem capUpperMassTarget (m : ℕ) (α : ℝ) (C : Cap m)
    (h : UniformTransverseExpansion m α) : CapUpperMassTarget m α C := by
  obtain ⟨Cexp, R₀, nu, hR₀, hR₀1, hh⟩ := h
  refine ⟨C.K, R₀, hR₀, fun R hR hRlt bd gsr => ?_⟩
  have hle := cap_mass_le hR C gsr
  have h0 := cap_mass_nonneg C gsr
  rw [abs_of_nonneg (mul_nonneg hR.le h0)]
  calc R * (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2) ≤ R * C.K :=
        mul_le_mul_of_nonneg_left hle hR.le
    _ = C.K * R := by ring

/-- **`eq:upper-J` of `lem:cap-upper`**, as the target of `Trial.lean`: the `J`-form is
`capJForm` (`eq:J-definition`) and `δ_R = R ν_R − m α`. -/
theorem capUpperJTarget (m : ℕ) (α : ℝ) (hm : 1 ≤ m) (C : Cap m)
    (hθ0 : 0 ≤ C.θ 0) (hθ1 : C.θ 0 ≤ 1) (h : UniformTransverseExpansion m α) :
    ∃ delta : ℝ → ℝ, CapUpperJTarget m α C (capJForm m α C) delta := by
  obtain ⟨Cexp, R₀, nu, hR₀, hR₀1, hh⟩ := h
  refine ⟨fun R => R * nu R - (m : ℝ) * α, ?_⟩
  refine ⟨|α| * capBdryConst m C Cexp + (m : ℝ) * |α| * capMassConst m C Cexp + Cexp * C.K,
    R₀, hR₀, fun R hR hRlt bd gsr => ?_⟩
  obtain ⟨hexp, hnu⟩ := hh R hR hRlt bd gsr
  have hk := cap_upper_J hm hR (le_of_lt (lt_of_lt_of_le hRlt hR₀1)) C hθ0 hθ1 hexp
  rw [hnu] at hk
  exact hk

/-! ## 15. The boundary energy of the trial function -/

theorem capLateralIntegral_const_mul (C : Cap m) (a : ℝ) (G : CapSpace m → ℝ) :
    capLateralIntegral C (fun p => a * G p) = a * capLateralIntegral C G := by
  have hpt : ∀ s, capLateralDensity C (fun p => a * G p) s = a * capLateralDensity C G s := by
    intro s
    rw [capLateralDensity, capLateralDensity, integral_const_mul]
    ring
  rw [capLateralIntegral, capLateralIntegral,
    setIntegral_congr_fun measurableSet_Ioo (fun s _ => hpt s), integral_const_mul]

theorem capLateralIntegral_congr (C : Cap m) {G H : CapSpace m → ℝ}
    (h : ∀ s ∈ Ioo (-C.K) 0, ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      G (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        = H (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))) :
    capLateralIntegral C G = capLateralIntegral C H := by
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [capLateralDensity, capLateralDensity]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => h s hs ω)

theorem capJterm_transLift (hR : 0 < R) (C : Cap m) (ψ : TransH1 m R) :
    capJterm C (transLift m R ψ)
      = R ^ m * (capLateralIntegral C (fun p => ψ.toFun (R • p.2) ^ 2)
          + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ψ.toFun (R • z) ^ 2) := by
  have hf : (fun p : CapSpace m => transLift m R ψ p.2 ^ 2)
      = fun p : CapSpace m => R ^ m * ψ.toFun (R • p.2) ^ 2 :=
    funext fun p => transLift_sq m hR ψ p.2
  have hd : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), transLift m R ψ z ^ 2)
      = R ^ m * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ψ.toFun (R • z) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun z _ => transLift_sq m hR ψ z
  rw [capJterm, hf, capLateralIntegral_const_mul, hd]
  ring

section Assembly

variable {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The boundary energy of the trial function** splits into the bulk tensor term and the two
cap `Γ`-integrals of `Ψ_R²`. -/
theorem boundaryEnergy_trialExt (hm : 1 ≤ m) (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    boundaryEnergy Cm Cp L R (trialExt Cm Cp L R F gsr.psi)
      = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
          * sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2)
        + F (-L/2 + Cm.K * R) ^ 2 * capJterm Cm (transLift m R gsr.psi)
        + F (L/2 - Cp.K * R) ^ 2 * capJterm Cp (transLift m R gsr.psi) := by
  have hab := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hcont : Continuous (trialExt Cm Cp L R F gsr.psi) :=
    continuous_trialExt hF.continuous gsr.psiC1.continuous hab.le
  have hsplit := boundaryEnergy_tensor_split_of_continuous' (Cm := Cm) (Cp := Cp) (L := L)
    (R := R) hm hR hL (trialExt Cm Cp L R F gsr.psi) F (fun z => gsr.psi.toFun z) hcont
    (fun x hx ω => trialExt_bulk hx.1.le hx.2.le)
  rw [hsplit, integral_Icc_eq_integral_Ioo]
  -- the left cap
  have hKmR : (0:ℝ) < Cm.K * R := mul_pos Cm.hK hR
  have hKpR : (0:ℝ) < Cp.K * R := mul_pos Cp.hK hR
  have hlatL : capLateralIntegral Cm (fun p => trialExt Cm Cp L R F gsr.psi
        (-L/2 - R * p.1, R • p.2) ^ 2)
      = capLateralIntegral Cm (fun p => F (-L/2 + Cm.K * R) ^ 2
          * gsr.psi.toFun (R • p.2) ^ 2) := by
    refine capLateralIntegral_congr Cm fun s hs ω => ?_
    have hlt : (-L/2 - R * s : ℝ) < -L/2 + Cm.K * R := by nlinarith [hs.1, hR]
    rw [trialExt_left (Cp := Cp) (F := F) (ψ := gsr.psi)
      (p := ((-L/2 - R * s : ℝ), R • (Cm.θ s • (ω : EuclideanSpace ℝ (Fin m))))) hlt]
    ring
  have hdiskL : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0),
        trialExt Cm Cp L R F gsr.psi (-L/2, R • z) ^ 2)
      = F (-L/2 + Cm.K * R) ^ 2
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), gsr.psi.toFun (R • z) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [trialExt_left (Cp := Cp) (F := F) (ψ := gsr.psi)
      (p := ((-L/2 : ℝ), R • z)) (by linarith)]
    ring
  have hlatR : capLateralIntegral Cp (fun p => trialExt Cm Cp L R F gsr.psi
        (L/2 + R * p.1, R • p.2) ^ 2)
      = capLateralIntegral Cp (fun p => F (L/2 - Cp.K * R) ^ 2
          * gsr.psi.toFun (R • p.2) ^ 2) := by
    refine capLateralIntegral_congr Cp fun s hs ω => ?_
    have hgt : L/2 - Cp.K * R < (L/2 + R * s : ℝ) := by nlinarith [hs.1, hR]
    rw [trialExt_right (Cm := Cm) (F := F) (ψ := gsr.psi)
      (p := ((L/2 + R * s : ℝ), R • (Cp.θ s • (ω : EuclideanSpace ℝ (Fin m)))))
      (le_of_lt (lt_trans hab hgt)) hgt]
    ring
  have hdiskR : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0),
        trialExt Cm Cp L R F gsr.psi (L/2, R • z) ^ 2)
      = F (L/2 - Cp.K * R) ^ 2
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), gsr.psi.toFun (R • z) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [trialExt_right (Cm := Cm) (F := F) (ψ := gsr.psi)
      (p := ((L/2 : ℝ), R • z)) (by linarith) (by linarith)]
    ring
  rw [hlatL, capLateralIntegral_const_mul, hdiskL, hlatR, capLateralIntegral_const_mul, hdiskR,
    capJterm_transLift hR Cm gsr.psi, capJterm_transLift hR Cp gsr.psi]
  ring

/-- The renormalized cap energy `R⁻¹‖∇Ψ_R‖² + J[Ψ_R] − δ_R‖Ψ_R‖²` of the unit cap. -/
def capEnergyTerm (m : ℕ) (α R : ℝ) (C : Cap m)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gsr : TransverseGroundStateReg m α R bd) : ℝ :=
  R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
    + capJForm m α C (capGroundLift m R gsr.psi)
    - (R * gsr.nu - (m : ℝ) * α) * ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2

/-- **`eq:trial-energy`, exact form.**  The renormalized energy of the trial function is the
axial Dirichlet energy plus the two cap terms; the bulk transverse contribution cancels exactly
by the weak eigenvalue equation for `ψ_R`. -/
theorem renormEnergy_trialH1P (hm : 1 ≤ m) (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd)
    (hbd : bd gsr.psi gsr.psi = sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2)) :
    renormEnergy Cm Cp L R α gsr.nu (trialH1P Cm Cp L hR hL F hF gsr)
      = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
        + F (-L/2 + Cm.K * R) ^ 2 * capEnergyTerm m α R Cm gsr
        + F (L/2 - Cp.K * R) ^ 2 * capEnergyTerm m α R Cp gsr := by
  have hRne : R ≠ 0 := hR.ne'
  -- the cap masses and energies in `Ψ_R` form
  have hmassCap : ∀ C : Cap m, (R ^ (m + 1) * ∫ p in C.body, gsr.psi.toFun (R • p.2) ^ 2)
      = R * ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2 := by
    intro C
    have h : (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
        = R ^ m * ∫ p in C.body, gsr.psi.toFun (R • p.2) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (measurableSet_capBody C)
        fun p _ => transLift_sq m hR gsr.psi p.2
    rw [h, pow_succ]
    ring
  have hdirCap : ∀ C : Cap m, (R ^ (m + 1) *
        ∫ p in C.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2)
      = R⁻¹ * ∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2 := by
    intro C
    have h : (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
        = R ^ m * R ^ 2 *
          ∫ p in C.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_capBody C) fun p _ => ?_
      rw [gradZP_capGroundLift gsr.psiC1, norm_classicalGrad_transLift_sq hR gsr.psiC1]
    rw [h]
    field_simp
    ring
  -- the Rayleigh identity
  have hray : Weak.dirichlet gsr.psi
      + α * sphereIntegral m R (fun z => gsr.psi.toFun z ^ 2) = gsr.nu := by
    have h := gsr.toTransverseGroundState.nu_eq_rayleigh
    rw [qB] at h
    rw [← hbd]
    exact h.symm
  rw [renormEnergy, dirichletP_trialH1P_normalized, massP_trialH1P_normalized,
    trialH1P_toFun, boundaryEnergy_trialExt hm Cm Cp L hR hL F hF gsr,
    massP_capTrialLeft_eq, massP_capTrialRight_eq,
    dirichletP_capTrialLeft_eq, dirichletP_capTrialRight_eq,
    hmassCap Cm, hmassCap Cp, hdirCap Cm, hdirCap Cp,
    capJterm_transLift hR Cm gsr.psi, capJterm_transLift hR Cp gsr.psi]
  rw [capEnergyTerm, capEnergyTerm, capJForm_capGroundLift, capJForm_capGroundLift,
    capJterm_transLift hR Cm gsr.psi, capJterm_transLift hR Cp gsr.psi, ← hray]
  ring

/-- **`eq:trial-mass`, exact form**: the mass of the trial function is the bulk mass `M[F]`
plus the two cap masses `R‖Ψ_R‖²_{L²(𝒞±)}`. -/
theorem massP_trialH1P_caps (Cm Cp : Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    massP (trialH1P Cm Cp L hR hL F hF gsr)
      = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
        + F (-L/2 + Cm.K * R) ^ 2 * (R * ∫ p in Cm.body, capGroundLift m R gsr.psi p ^ 2)
        + F (L/2 - Cp.K * R) ^ 2
            * (R * ∫ p in Cp.body, capGroundLift m R gsr.psi p ^ 2) := by
  have hmassCap : ∀ C : Cap m, (R ^ (m + 1) * ∫ p in C.body, gsr.psi.toFun (R • p.2) ^ 2)
      = R * ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2 := by
    intro C
    have h : (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
        = R ^ m * ∫ p in C.body, gsr.psi.toFun (R • p.2) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (measurableSet_capBody C)
        fun p _ => transLift_sq m hR gsr.psi p.2
    rw [h, pow_succ]
    ring
  rw [massP_trialH1P_normalized, massP_capTrialLeft_eq, massP_capTrialRight_eq,
    hmassCap Cm, hmassCap Cp]
  ring

/-- **`eq:trial-mass`**: `M[F] ≤ N_R[𝒯_RF] ≤ M[F] + C R S[F]`. -/
theorem trialMassTarget (m : ℕ) (α : ℝ) (Cm Cp : Cap m) (L : ℝ)
    (h : UniformTransverseExpansion m α) : TrialMassTarget m α Cm Cp L := by
  obtain ⟨Cexp, R₀, nu, hR₀, hR₀1, hh⟩ := h
  refine ⟨Cm.K + Cp.K, R₀, hR₀, fun R hR hRlt hL bd gsr F hF => ?_⟩
  have hmass := massP_trialH1P_caps Cm Cp L hR hL F hF gsr
  have h1 := cap_mass_le hR Cm gsr
  have h2 := cap_mass_le hR Cp gsr
  have h01 := cap_mass_nonneg Cm gsr
  have h02 := cap_mass_nonneg Cp gsr
  have hsm := sq_nonneg (F (-L/2 + Cm.K * R))
  have hsp := sq_nonneg (F (L/2 - Cp.K * R))
  have hKm := Cm.hK.le
  have hKp := Cp.hK.le
  constructor
  · rw [hmass]
    linarith [mul_nonneg hsm (mul_nonneg hR.le h01), mul_nonneg hsp (mul_nonneg hR.le h02)]
  · rw [hmass]
    have hA : F (-L/2 + Cm.K * R) ^ 2
        * (R * ∫ p in Cm.body, capGroundLift m R gsr.psi p ^ 2)
        ≤ (Cm.K + Cp.K) * R * F (-L/2 + Cm.K * R) ^ 2 := by
      have hMle : (∫ p in Cm.body, capGroundLift m R gsr.psi p ^ 2) ≤ Cm.K + Cp.K := by
        linarith [h1, hKp]
      calc F (-L/2 + Cm.K * R) ^ 2 * (R * ∫ p in Cm.body, capGroundLift m R gsr.psi p ^ 2)
          ≤ F (-L/2 + Cm.K * R) ^ 2 * (R * (Cm.K + Cp.K)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMle hR.le) hsm
        _ = (Cm.K + Cp.K) * R * F (-L/2 + Cm.K * R) ^ 2 := by ring
    have hB : F (L/2 - Cp.K * R) ^ 2
        * (R * ∫ p in Cp.body, capGroundLift m R gsr.psi p ^ 2)
        ≤ (Cm.K + Cp.K) * R * F (L/2 - Cp.K * R) ^ 2 := by
      have hMle : (∫ p in Cp.body, capGroundLift m R gsr.psi p ^ 2) ≤ Cm.K + Cp.K := by
        linarith [h2, hKm]
      calc F (L/2 - Cp.K * R) ^ 2 * (R * ∫ p in Cp.body, capGroundLift m R gsr.psi p ^ 2)
          ≤ F (L/2 - Cp.K * R) ^ 2 * (R * (Cm.K + Cp.K)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMle hR.le) hsp
        _ = (Cm.K + Cp.K) * R * F (L/2 - Cp.K * R) ^ 2 := by ring
    linarith [hA, hB]

/-- The cap energy term is `β(𝒞) + O(R)`. -/
theorem capEnergyTerm_sub_beta (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1) (C : Cap m)
    (hθ0 : 0 ≤ C.θ 0) (hθ1 : C.θ 0 ≤ 1)
    {gsr : TransverseGroundStateReg m α R bd} {Cexp : ℝ}
    (hexp : TransverseExpansionData m α R gsr Cexp) :
    |capEnergyTerm m α R C gsr - Cap.beta C α|
      ≤ (C.K * Cexp ^ 2 + (|α| * capBdryConst m C Cexp
          + (m : ℝ) * |α| * capMassConst m C Cexp + Cexp * C.K)) * R := by
  have hgr := cap_upper_gradient C hexp
  have hgr0 : (0:ℝ) ≤ ∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_capBody C) fun _ _ => by positivity
  have hRinv : (0:ℝ) ≤ R⁻¹ := by positivity
  have hgrR : R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
      ≤ C.K * Cexp ^ 2 * R := by
    calc R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
        ≤ R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) := mul_le_mul_of_nonneg_left hgr hRinv
      _ = C.K * Cexp ^ 2 * R := by field_simp
  have hJ := cap_upper_J hm hR hR1 C hθ0 hθ1 hexp
  have heq : capEnergyTerm m α R C gsr - Cap.beta C α
      = R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
        + (capJForm m α C (capGroundLift m R gsr.psi)
            - (R * gsr.nu - (m : ℝ) * α) * (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
            - Cap.beta C α) := by
    rw [capEnergyTerm]; ring
  rw [heq]
  calc |R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)
        + (capJForm m α C (capGroundLift m R gsr.psi)
            - (R * gsr.nu - (m : ℝ) * α) * (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
            - Cap.beta C α)|
      ≤ |R⁻¹ * (∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2)|
        + |capJForm m α C (capGroundLift m R gsr.psi)
            - (R * gsr.nu - (m : ℝ) * α) * (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
            - Cap.beta C α| := abs_add_le _ _
    _ ≤ C.K * Cexp ^ 2 * R + (|α| * capBdryConst m C Cexp
        + (m : ℝ) * |α| * capMassConst m C Cexp + Cexp * C.K) * R := by
        rw [abs_of_nonneg (mul_nonneg hRinv hgr0)]
        exact add_le_add hgrR hJ
    _ = (C.K * Cexp ^ 2 + (|α| * capBdryConst m C Cexp
        + (m : ℝ) * |α| * capMassConst m C Cexp + Cexp * C.K)) * R := by ring

/-- **`eq:trial-energy`**: `E_R[𝒯_RF] = a_{β₋,β₊;I_R}[F] + ε_R[F]`, `|ε_R[F]| ≤ C R S[F]`. -/
theorem trialEnergyTarget (m : ℕ) (α : ℝ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L : ℝ)
    (hθ0m : 0 ≤ Cm.θ 0) (hθ1m : Cm.θ 0 ≤ 1) (hθ0p : 0 ≤ Cp.θ 0) (hθ1p : Cp.θ 0 ≤ 1)
    (h : UniformTransverseExpansion m α) : TrialEnergyTarget m α Cm Cp L := by
  obtain ⟨Cexp, R₀, nu, hR₀, hR₀1, hh⟩ := h
  refine ⟨max (Cm.K * Cexp ^ 2 + (|α| * capBdryConst m Cm Cexp
      + (m : ℝ) * |α| * capMassConst m Cm Cexp + Cexp * Cm.K))
    (Cp.K * Cexp ^ 2 + (|α| * capBdryConst m Cp Cexp
      + (m : ℝ) * |α| * capMassConst m Cp Cexp + Cexp * Cp.K)),
    R₀, hR₀, fun R hR hRlt hL bd gsr F hF => ?_⟩
  obtain ⟨hexp, hnu⟩ := hh R hR hRlt bd gsr
  have hR1 : R ≤ 1 := le_of_lt (lt_of_lt_of_le hRlt hR₀1)
  rw [renormEnergy_trialH1P hm Cm Cp L hR hL F hF gsr hexp.bdSphere]
  set Am : ℝ := Cm.K * Cexp ^ 2 + (|α| * capBdryConst m Cm Cexp
      + (m : ℝ) * |α| * capMassConst m Cm Cexp + Cexp * Cm.K) with hAm
  set Ap : ℝ := Cp.K * Cexp ^ 2 + (|α| * capBdryConst m Cp Cexp
      + (m : ℝ) * |α| * capMassConst m Cp Cexp + Cexp * Cp.K) with hAp
  have hEm := capEnergyTerm_sub_beta hm hR hR1 Cm hθ0m hθ1m hexp
  have hEp := capEnergyTerm_sub_beta hm hR hR1 Cp hθ0p hθ1p hexp
  rw [← hAm] at hEm
  rw [← hAp] at hEp
  have hsplit : ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
        + F (-L/2 + Cm.K * R) ^ 2 * capEnergyTerm m α R Cm gsr
        + F (L/2 - Cp.K * R) ^ 2 * capEnergyTerm m α R Cp gsr)
      - ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
        + Cap.beta Cm α * F (-L/2 + Cm.K * R) ^ 2
        + Cap.beta Cp α * F (L/2 - Cp.K * R) ^ 2)
      = F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm m α R Cm gsr - Cap.beta Cm α)
        + F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm m α R Cp gsr - Cap.beta Cp α) := by
    ring
  rw [hsplit]
  have hsm := sq_nonneg (F (-L/2 + Cm.K * R))
  have hsp := sq_nonneg (F (L/2 - Cp.K * R))
  have hAmle : Am ≤ max Am Ap := le_max_left _ _
  have hAple : Ap ≤ max Am Ap := le_max_right _ _
  have hb1 : |F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm m α R Cm gsr - Cap.beta Cm α)|
      ≤ F (-L/2 + Cm.K * R) ^ 2 * (max Am Ap * R) := by
    rw [abs_mul, abs_of_nonneg hsm]
    refine mul_le_mul_of_nonneg_left (hEm.trans ?_) hsm
    exact mul_le_mul_of_nonneg_right hAmle hR.le
  have hb2 : |F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm m α R Cp gsr - Cap.beta Cp α)|
      ≤ F (L/2 - Cp.K * R) ^ 2 * (max Am Ap * R) := by
    rw [abs_mul, abs_of_nonneg hsp]
    refine mul_le_mul_of_nonneg_left (hEp.trans ?_) hsp
    exact mul_le_mul_of_nonneg_right hAple hR.le
  calc |F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm m α R Cm gsr - Cap.beta Cm α)
        + F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm m α R Cp gsr - Cap.beta Cp α)|
      ≤ |F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm m α R Cm gsr - Cap.beta Cm α)|
        + |F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm m α R Cp gsr - Cap.beta Cp α)| :=
        abs_add_le _ _
    _ ≤ F (-L/2 + Cm.K * R) ^ 2 * (max Am Ap * R)
        + F (L/2 - Cp.K * R) ^ 2 * (max Am Ap * R) := add_le_add hb1 hb2
    _ = max Am Ap * R * (F (-L/2 + Cm.K * R) ^ 2 + F (L/2 - Cp.K * R) ^ 2) := by ring

end Assembly

end

/-! ## 16. Axiom audit -/


end RobinCaps.ThinDomain
