import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Checks

/-!
# A general flat-cap perturbation (paper Section 9.3)

This file generalizes `RobinCaps/Cap/Frustum.lean` from the linear profile
`χ(s) = s + 1` to an arbitrary nonnegative, nondecreasing, convex, Lipschitz
(`W^{1,∞}`) profile `χ : [-K,0] → ℝ` with `χ(-K) = 0`.  For small `δ > 0` the
profile `θ_δ(s) = 1 - δ·χ(s)` is an admissible cap profile, and
`β(C_δ)/α = F(C_δ)/ω_m = 1 - κδ + O(δ²)` with `κ = m(χ(0) - ∫_{-K}^0 χ)`
(`Cap.kappa`).  If `κ > 0` then `β(C_δ) < α` for all small `δ > 0`.

The key difference from `Frustum.lean` is that `χ` here is merely Lipschitz,
not `C¹`: `Checks.lean`'s `linearization_decomposition` / `linearization_bound`
assume `χ ∈ C¹` (`HasDerivAt` everywhere with continuous derivative).  Part 1
below reproves the linearization bound assuming only that `deriv χ` is
bounded on `[-K,0]` (no continuity of `deriv χ` is needed): `deriv χ` is
*always* measurable (`measurable_deriv`), and a bounded measurable function on
a bounded interval is interval integrable.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

/-! ## Part 1: linearization for Lipschitz `χ` (no `C¹` hypothesis) -/

/-- **Observation (a).** The derivative of `s ↦ 1 - δ·χ(s)` at any point, for
any real (not necessarily differentiable) `χ`, is `-(δ · deriv χ s)`. -/
theorem deriv_one_sub_lip_pf (δ : ℝ) (χ : ℝ → ℝ) (s : ℝ) :
    deriv (fun s => 1 - δ * χ s) s = -(δ * deriv χ s) := by
  by_cases hδ : δ = 0
  · simp [hδ]
  · by_cases hd : DifferentiableAt ℝ χ s
    · have h : HasDerivAt (fun s => 1 - δ * χ s) (0 - δ * deriv χ s) s := by
        have hχ' : HasDerivAt χ (deriv χ s) s := hd.hasDerivAt
        have := hχ'.const_mul δ
        simpa using (hasDerivAt_const (x := s) (c := (1 : ℝ))).sub this
      rw [h.deriv]; ring
    · have hd2 : ¬ DifferentiableAt ℝ (fun s => 1 - δ * χ s) s := by
        intro hcontra
        apply hd
        have heq : χ = fun t => (1 - (1 - δ * χ t)) / δ := by
          funext t; field_simp; ring
        rw [heq]
        exact (hcontra.const_sub (1 : ℝ)).div_const δ
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd2]
      ring

/-- **Observation (c).** The product of a function continuous on `[-K,0]` with a
globally measurable function bounded on `[-K,0]` is interval integrable on
`(-K)..0`.  Applied with the measurable factor `= deriv χ` (always measurable,
`measurable_deriv`), this replaces the continuity-of-`χ'`-based integrability
arguments of `Checks.lean` by boundedness-based ones. -/
theorem intervalIntegrable_mul_bounded_measurable_pf {K : ℝ} (hK : 0 < K)
    {g h : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc (-K) 0))
    (hh : Measurable h) {C : ℝ} (hhC : ∀ s ∈ Set.Icc (-K) 0, |h s| ≤ C) :
    IntervalIntegrable (fun s => g s * h s) volume (-K) 0 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (neg_nonpos.mpr hK.le)]
  have hmeas : MeasurableSet (Set.Ioc (-K : ℝ) 0) := measurableSet_Ioc
  have hgIoc : ContinuousOn g (Set.Ioc (-K) 0) := hg.mono Set.Ioc_subset_Icc_self
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc (-K) 0)) :=
    hgIoc.aestronglyMeasurable hmeas
  have hhmeas : AEStronglyMeasurable h (volume.restrict (Set.Ioc (-K) 0)) :=
    hh.aestronglyMeasurable.restrict
  obtain ⟨Cg, hCg⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hg
  refine IntegrableOn.of_bound measure_Ioc_lt_top (hgmeas.mul hhmeas) (Cg * C) ?_
  filter_upwards [ae_restrict_mem hmeas] with s hs
  have hsIcc : s ∈ Set.Icc (-K) 0 := ⟨hs.1.le, hs.2⟩
  have hCg0 : (0 : ℝ) ≤ Cg := (abs_nonneg (g s)).trans (hCg s hsIcc)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCg s hsIcc) (hhC s hsIcc) (abs_nonneg _) hCg0

set_option maxHeartbeats 1600000 in
/-- **Linearization decomposition for Lipschitz `χ`** (generalizes
`linearization_decomposition`, replacing the `C¹` hypothesis on `χ` with
boundedness of `deriv χ` on `[-K,0]`). -/
theorem linearization_decomposition_lip_pf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (χ : ℝ → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hχcont : ContinuousOn χ (Set.Icc (-K) 0)) (M' : ℝ)
    (hχ'bound : ∀ s ∈ Set.Icc (-K) 0, |deriv χ s| ≤ M') :
    revF m K (fun s => 1 - δ * χ s) / omega m
      = (1 - δ * χ 0) ^ m
        + (m : ℝ) * δ * (∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
        + (m : ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
            / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1)) := by
  have hKle : (-K : ℝ) ≤ 0 := neg_nonpos.mpr hK.le
  have huIcc : Set.uIcc (-K) 0 = Set.Icc (-K) 0 := Set.uIcc_of_le hKle
  set θ : ℝ → ℝ := fun s => 1 - δ * χ s with hθdef
  have hθcont : ContinuousOn θ (Set.Icc (-K) 0) := by
    rw [hθdef]; fun_prop
  have hderivθ_eq : ∀ s, deriv θ s = -(δ * deriv χ s) := by
    intro s; rw [hθdef]; exact deriv_one_sub_lip_pf δ χ s
  let f1 : ℝ → ℝ := fun s => χ s * (θ s) ^ (m - 1)
  let f2 : ℝ → ℝ := fun s => (θ s) ^ (m - 1) * (deriv χ s) ^ 2
      / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1)
  have hf1cont : ContinuousOn f1 (Set.Icc (-K) 0) := by
    change ContinuousOn (fun s => χ s * (θ s) ^ (m - 1)) (Set.Icc (-K) 0)
    fun_prop
  rw [← huIcc] at hθcont hf1cont
  have hint1 : IntervalIntegrable
      (fun s => (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2)) volume (-K) 0 := by
    rw [huIcc] at hθcont
    refine intervalIntegrable_mul_bounded_measurable_pf hK (C := Real.sqrt (1 + (δ * M') ^ 2))
      (hθcont.pow _) (by fun_prop) ?_
    intro s hs
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have hb : |δ * deriv χ s| ≤ δ * M' := by
      rw [abs_mul, abs_of_nonneg hδ0]
      exact mul_le_mul_of_nonneg_left (hχ'bound s hs) hδ0
    have hsq : (δ * deriv χ s) ^ 2 ≤ (δ * M') ^ 2 := by
      nlinarith [sq_abs (δ * deriv χ s), hb, abs_nonneg (δ * deriv χ s)]
    rw [hderivθ_eq s, neg_sq]
    linarith [hsq]
  have hint2 : IntervalIntegrable (fun s => (θ s) ^ m) volume (-K) 0 :=
    (hθcont.pow _).intervalIntegrable
  have hintf1 : IntervalIntegrable f1 volume (-K) 0 := hf1cont.intervalIntegrable
  have hintf2 : IntervalIntegrable f2 volume (-K) 0 := by
    rw [huIcc] at hθcont
    have := intervalIntegrable_mul_bounded_measurable_pf hK (C := M' ^ 2) (hθcont.pow (m - 1))
      (h := fun s => (deriv χ s) ^ 2 / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))
      (by fun_prop) ?_
    · simp only [f2, mul_div_assoc]
      exact this
    · intro s hs
      have hsq : (deriv χ s) ^ 2 ≤ M' ^ 2 := by
        have h := hχ'bound s hs
        nlinarith [abs_nonneg (deriv χ s), sq_abs (deriv χ s)]
      have hden : (1 : ℝ) ≤ Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1 :=
        by linarith [Real.sqrt_nonneg (1 + (δ * deriv χ s) ^ 2)]
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hsq, hden]
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
      have hd := hderivθ_eq s
      have hid := integrand_identity' m hm δ (χ s) (deriv χ s)
      have hθs : θ s = 1 - δ * χ s := by rw [hθdef]
      rw [hd, hθs, hid]
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
  have hf2eq : (∫ s in (-K)..0, f2 s) = ∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s)^2
      / (Real.sqrt (1 + (δ * deriv χ s)^2) + 1) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    simp only [f2, hθdef]
  rw [hrev, hkey]
  simp only [hf1eq, hf2eq]
  have hθ0 : θ 0 = 1 - δ * χ 0 := by rw [hθdef]
  rw [hθ0]
  ring

set_option maxHeartbeats 1600000 in
/-- **Part 1 target.** The linearization bound `β(C_δ)/α = F(C_δ)/ω_m = 1 - κδ + O(δ²)`
for a merely Lipschitz `χ` (generalizes `linearization_bound`, replacing the `C¹`
hypothesis on `χ` with boundedness of `deriv χ` on `[-K,0]`). -/
theorem linearization_bound_lip_pf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (χ : ℝ → ℝ) (M M' : ℝ)
    (hχcont : ContinuousOn χ (Set.Icc (-K) 0))
    (hχnn : ∀ s ∈ Set.Icc (-K) 0, 0 ≤ χ s)
    (hχbound : ∀ s ∈ Set.Icc (-K) 0, χ s ≤ M)
    (hχ'bound : ∀ s ∈ Set.Icc (-K) 0, |deriv χ s| ≤ M')
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
    have hdec := linearization_decomposition_lip_pf m hm K hK χ δ hδ0 hχcont M' hχ'bound
    have hff : revF m K (fun s => 1 - δ * χ s) / omega m - (1 - kappa m K χ * δ)
        = ((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
          + (m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))
          + (m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
              / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1)) := by
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
    have hintB : IntervalIntegrable (fun s => (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
        / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1)) volume (-K) 0 := by
      have := intervalIntegrable_mul_bounded_measurable_pf hK (C := M'^2) (hθcont.pow (m - 1))
        (h := fun s => (deriv χ s) ^ 2 / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))
        (by fun_prop) ?_
      · simpa only [mul_div_assoc] using this
      · intro s hs
        have hsq : (deriv χ s) ^ 2 ≤ M' ^ 2 := by
          have h := hχ'bound s hs
          nlinarith [abs_nonneg (deriv χ s), sq_abs (deriv χ s)]
        have hden : (1 : ℝ) ≤ Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1 :=
          by linarith [Real.sqrt_nonneg (1 + (δ * deriv χ s) ^ 2)]
        rw [abs_of_nonneg (by positivity)]
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hsq, hden]
    have hBbound : |(∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
        / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))| ≤ M'^2 * K := by
      have hle : ∀ s ∈ Ι (-K) 0, ‖(1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
          / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1)‖ ≤ M'^2 := by
        intro s hs
        have hsIcc : s ∈ Set.Icc (-K) 0 := by
          rw [Set.uIoc_of_le (neg_nonpos.mpr hK.le)] at hs
          exact ⟨le_of_lt hs.1, hs.2⟩
        have hχs0 : 0 ≤ χ s := hχnn s hsIcc
        have hθle : 1 - δ * χ s ≤ 1 := by nlinarith [mul_nonneg hδ0 hχs0]
        have hθ0 : 0 ≤ 1 - δ * χ s := by nlinarith [hδM, hχbound s hsIcc, hM]
        have hpow0 : 0 ≤ (1 - δ * χ s) ^ (m-1) := pow_nonneg hθ0 _
        have hpow1 : (1 - δ * χ s) ^ (m-1) ≤ 1 := pow_le_one₀ hθ0 hθle
        have hsq : (deriv χ s)^2 ≤ M'^2 := by
          have h := hχ'bound s hsIcc
          nlinarith [abs_nonneg (deriv χ s), sq_abs (deriv χ s), h, hM']
        have hden : 1 ≤ Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1 := by
          have : (0:ℝ) ≤ (δ * deriv χ s)^2 := sq_nonneg _
          have := Real.sqrt_nonneg (1 + (δ * deriv χ s)^2)
          linarith
        rw [Real.norm_eq_abs, abs_div,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - δ*χ s)^(m-1) * (deriv χ s)^2),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.sqrt (1 + (δ*deriv χ s)^2)+1)]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt (1 + (δ*deriv χ s)^2)+1)]
        have h1 : (1 - δ*χ s)^(m-1) * (deriv χ s)^2 ≤ 1 * M'^2 := by
          exact mul_le_mul hpow1 hsq (sq_nonneg _) (by norm_num)
        nlinarith [h1, hden]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
      rwa [show |0 - (-K)| = K by rw [abs_of_nonneg (by linarith)]; ring] at h
    rw [hff]
    have htri : |((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
          + (m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))
          + (m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
              / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))|
        ≤ |(1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0)|
          + |(m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))|
          + |(m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
              / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))| := by
      have h1 := abs_add_le (((1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0))
          + (m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s)))
        ((m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
              / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1)))
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
    have hB2 : |(m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
              / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))|
        ≤ (m:ℝ) * δ ^ 2 * (M'^2 * K) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hmK0 (sq_nonneg δ))]
      exact mul_le_mul_of_nonneg_left hBbound (mul_nonneg hmK0 (sq_nonneg δ))
    calc |(1 - δ * χ 0) ^ m - 1 + (m:ℝ) * (δ * χ 0)|
          + |(m:ℝ) * δ * ((∫ s in (-K)..0, χ s * (1 - δ * χ s) ^ (m - 1))
              - (∫ s in (-K)..0, χ s))|
          + |(m:ℝ) * δ ^ 2 * (∫ s in (-K)..0, (1 - δ * χ s) ^ (m - 1) * (deriv χ s) ^ 2
              / (Real.sqrt (1 + (δ * deriv χ s) ^ 2) + 1))|
        ≤ (m:ℝ)^2 * M^2 * δ^2 + (m:ℝ) * δ * (M^2 * ((m-1:ℕ):ℝ) * δ * K)
          + (m:ℝ) * δ ^ 2 * (M'^2 * K) := by
          exact add_le_add (add_le_add hP hA2) hB2
      _ = ((m:ℝ)^2 * M^2 + (m:ℝ) * M^2 * ((m-1:ℕ):ℝ) * K + (m:ℝ) * M'^2 * K) * δ^2 := by
          ring

/-! ## Part 2: the perturbed-flat cap -/

/-- The hypotheses on `χ` making `θ_δ = 1 - δ·χ` an admissible perturbation of the
flat cap (paper Section 9.3): `χ` is continuous, vanishes at the entrance, is
nonnegative, nondecreasing and convex on `[-K,0]`, and `M`, `M'` are sup-bounds
for `χ` and `deriv χ` used in the linearization estimate of Part 1. -/
structure FlatPerturbation (K : ℝ) (χ : ℝ → ℝ) (M M' : ℝ) : Prop where
  cont : ContinuousOn χ (Set.Icc (-K) 0)
  zero : χ (-K) = 0
  nonneg : ∀ s ∈ Set.Icc (-K) 0, 0 ≤ χ s
  mono : MonotoneOn χ (Set.Icc (-K) 0)
  convex : ConvexOn ℝ (Set.Icc (-K) 0) χ
  bound : ∀ s ∈ Set.Icc (-K) 0, χ s ≤ M
  lip : ∀ s ∈ Set.Icc (-K) 0, |deriv χ s| ≤ M'
  hM : 0 ≤ M
  hM' : 0 ≤ M'

/-- **The perturbed-flat cap.**  For `0 ≤ δ` with `δM ≤ 1/2`, the profile
`θ_δ(s) = 1 - δ·χ(s)` defines an admissible cap of axial length `K`. -/
noncomputable def perturbedFlat (m : ℕ) (K : ℝ) (hK : 0 < K) (χ : ℝ → ℝ) {M M' : ℝ}
    (h : FlatPerturbation K χ M M') (δ : ℝ) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 2) : Cap m where
  K := K
  hK := hK
  θ := fun s => 1 - δ * χ s
  θ_pos := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (-K) 0 := Set.Ioo_subset_Icc_self hs
    have hle : δ * χ s ≤ δ * M := mul_le_mul_of_nonneg_left (h.bound s hsIcc) hδ0
    have hh : δ * χ s ≤ 1 / 2 := le_trans hle hδM
    linarith
  θ_le_one := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (-K) 0 := Set.Ioo_subset_Icc_self hs
    have hh : 0 ≤ δ * χ s := mul_nonneg hδ0 (h.nonneg s hsIcc)
    linarith
  θ_concave := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxIcc : x ∈ Set.Icc (-K) 0 := Set.Ioo_subset_Icc_self hx
    have hyIcc : y ∈ Set.Icc (-K) 0 := Set.Ioo_subset_Icc_self hy
    have hconv := h.convex.2 hxIcc hyIcc ha hb hab
    simp only [smul_eq_mul] at hconv ⊢
    nlinarith [mul_le_mul_of_nonneg_left hconv hδ0]
  θ_antitone := by
    intro a ha b hb hab
    have haIcc : a ∈ Set.Icc (-K) 0 := Set.Ioo_subset_Icc_self ha
    have hbIcc : b ∈ Set.Icc (-K) 0 := Set.Ioo_subset_Icc_self hb
    have hmono := h.mono haIcc hbIcc hab
    simp only
    nlinarith [mul_le_mul_of_nonneg_left hmono hδ0]
  θ_tendsto := by
    have hmemK : Set.Icc (-K) (0:ℝ) ∈ 𝓝[>] (-K) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT (by linarith : (-K:ℝ) < 0)) Set.Ioc_subset_Icc_self
    have hcw : ContinuousWithinAt χ (Set.Icc (-K) 0) (-K) :=
      h.cont (-K) (Set.left_mem_Icc.2 (by linarith))
    have hlim : Filter.Tendsto χ (𝓝[>] (-K)) (𝓝 (χ (-K))) :=
      hcw.mono_left (nhdsWithin_le_iff.2 hmemK)
    rw [h.zero] at hlim
    have hres := (tendsto_const_nhds (α := ℝ) (x := (1:ℝ))).sub (hlim.const_mul δ)
    simpa using hres
  θ_entrance := by
    show 1 - δ * χ (-K) = 1
    rw [h.zero]; ring
  θ_terminal := by
    have hmem0 : Set.Icc (-K) (0:ℝ) ∈ 𝓝[<] (0:ℝ) := by
      have hI : Set.Ioi (-K) ∈ 𝓝[<] (0:ℝ) :=
        mem_nhdsWithin_of_mem_nhds
          (isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith))
      filter_upwards [self_mem_nhdsWithin, hI] with z hz1 hz2
      exact ⟨le_of_lt hz2, le_of_lt hz1⟩
    have hcw0 : ContinuousWithinAt χ (Set.Icc (-K) 0) 0 :=
      h.cont 0 (Set.right_mem_Icc.2 (by linarith))
    have hlim0 : Filter.Tendsto χ (𝓝[<] (0:ℝ)) (𝓝 (χ 0)) :=
      hcw0.mono_left (nhdsWithin_le_iff.2 hmem0)
    exact (tendsto_const_nhds (α := ℝ) (x := (1:ℝ))).sub (hlim0.const_mul δ)

/-- The `F` of the perturbed-flat cap equals the raw `revF` formula. -/
theorem perturbedFlat_F_eq_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (χ : ℝ → ℝ) {M M' : ℝ}
    (h : FlatPerturbation K χ M M') (δ : ℝ) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 2) :
    (perturbedFlat m K hK χ h δ hδ0 hδM).F = revF m K (fun s => 1 - δ * χ s) := by
  rw [F_eq_revolutionF, revF_eq]
  rfl

/-! ## Part 3: strict decrease of `β` for small amplitudes -/

/-- **The perturbed-flat cap's effective end coefficient `β(C_δ)` is strictly
below `α` for all small amplitudes `0 < δ < δ₀`**, provided the linearized
coefficient `κ = m(χ(0) - ∫_{-K}^0 χ)` is positive.  This is the paper's
headline claim of Section 9.3 in explicit form. -/
theorem perturbedFlat_beta_lt_pf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (χ : ℝ → ℝ)
    {M M' : ℝ} (h : FlatPerturbation K χ M M') (hκ : 0 < kappa m K χ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (δ : ℝ) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 2),
      0 < δ → δ < δ₀ → ∀ α : ℝ, 0 < α →
        (perturbedFlat m K hK χ h δ hδ0 hδM).beta α < α := by
  obtain ⟨C, hC0, hbound⟩ := linearization_bound_lip_pf m hm K hK χ M M'
    h.cont h.nonneg h.bound h.lip h.hM h.hM'
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  refine ⟨kappa m K χ / (C + 1), by positivity, ?_⟩
  intro δ hδ0 hδM hδpos hδlt α hα
  have hb := hbound δ hδ0 hδM
  have hδlt' : δ * (C + 1) < kappa m K χ := (lt_div_iff₀ hCpos).mp hδlt
  have hCδ : C * δ < kappa m K χ := by nlinarith [hδlt']
  have hCδ2 : C * δ ^ 2 < kappa m K χ * δ := by
    have hmul := mul_lt_mul_of_pos_right hCδ hδpos
    calc C * δ ^ 2 = C * δ * δ := by ring
      _ < kappa m K χ * δ := hmul
  have hratio : revF m K (fun s => 1 - δ * χ s) / omega m < 1 := by
    have h1 := (abs_le.mp hb).2
    nlinarith [hCδ2]
  have hFlt : (perturbedFlat m K hK χ h δ hδ0 hδM).F < omega m := by
    rw [perturbedFlat_F_eq_pf]
    exact (div_lt_one (omega_pos m)).mp hratio
  have hpos : 0 < α / omega m := div_pos hα (omega_pos m)
  have hmul := mul_lt_mul_of_pos_left hFlt hpos
  rw [div_mul_cancel₀ α (omega_ne_zero m)] at hmul
  rw [beta]
  exact hmul

end

end Cap
end RobinCaps
