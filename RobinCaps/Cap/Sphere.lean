import Mathlib
import RobinCaps.Cap.Checks

/-!
# Sphere slicing and the general-`m` hemisphere

This file closes the sphere-slicing / general-`m` hemisphere identities that were
left as explicit targets in `RobinCaps.Cap.Checks`:

* `sphereSlicingTarget : SphereSlicingTarget m`, i.e.
  `ω_{m+1} = 2 ω_m ∫_{-1}^0 (1-s²)^{m/2} ds` for every `m : ℕ`;
* the volume and area of the general-`m` hemisphere,
  `|C| = ω_{m+1}/2` and `|Γ| = (m+1) ω_{m+1}/2`, and consequently
  `𝓕 = ω_{m+1}/2`.

The proofs are elementary and avoid any measure-theoretic slicing theorem:

* `omega_eq_gamma` evaluates `ω_k` through mathlib's `EuclideanSpace.volume_ball`
  and `Real.Gamma`; the `k = 0` case is `omega_zero`.
* `omega_rec` gives the two-step recurrence `ω_{k+2} = 2π/(k+2) ω_k`.
* `sphereSlice_eq_cos` rewrites the slice integral as `∫_0^{π/2} cos^{m+1}` via the
  change of variables `t = sin θ`; `sphereSlice_rec` is then the classical
  reduction formula for `∫ cosⁿ`.
* `sphereSlicingTarget` follows by two-step induction.

The area identity uses the a.e. identity
`(semi 1 s)^{m-1} √(1 + (deriv (semi 1) s)²) = (semi 1 s)^{m-2}` on `(-1,0)`
together with `semi_pow_integral` and `sphereSlice_rec`.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

/-! ## `ω_0 = 1` -/

/-- The volume of the unit ball in dimension `0` is `1`. -/
theorem omega_zero : omega 0 = 1 := by
  rw [omega]
  have hball : (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) (1 : ℝ)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Metric.mem_ball, dist_zero_right]
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx, norm_zero]
    norm_num
  rw [hball]
  have hpar : parallelepiped (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 0))).toBasis =
      Set.univ := by
    rw [parallelepiped_basis_eq]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    haveI : IsEmpty (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)))) := by
      rw [hfin]; infer_instance
    intro i
    exact isEmptyElim i
  have h1 : volume (parallelepiped (stdOrthonormalBasis ℝ
      (EuclideanSpace ℝ (Fin 0))).toBasis) = 1 := by
    rw [show (volume : Measure (EuclideanSpace ℝ (Fin 0))) =
      (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 0))).toBasis.addHaar from rfl]
    exact Module.Basis.addHaar_self _
  rw [hpar] at h1
  rw [h1]
  simp

/-! ## `ω_k = π^{k/2} / Γ(k/2+1)` -/

/-- The Gamma formula for the volume of the unit ball, for `k ≥ 1`. -/
theorem omega_eq_gamma (k : ℕ) (hk : 1 ≤ k) :
    omega k = (Real.sqrt Real.pi) ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  rw [omega, EuclideanSpace.volume_ball (Fin k) (0 : EuclideanSpace ℝ (Fin k)) 1]
  rw [Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal
    (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (le_of_lt (Real.Gamma_pos_of_pos (by positivity))))]

/-- `ω₂ = π`. -/
theorem omega_two : omega 2 = Real.pi := by
  rw [omega_eq_gamma 2 (by norm_num)]
  have harg : ((2 : ℕ) : ℝ) / 2 + 1 = (2 : ℝ) := by norm_num
  rw [harg]
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial 1]
    norm_num
  rw [hg, div_one]
  rw [Real.sq_sqrt Real.pi_nonneg]

/-! ## The two-step recurrence for `ω` -/

/-- Two-step recurrence `ω_{k+2} = (2π/(k+2)) ω_k`. -/
theorem omega_rec (k : ℕ) : omega (k + 2) = 2 * Real.pi / (k + 2) * omega k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [omega_two, omega_zero]
    norm_num
  · have h2 := omega_eq_gamma (k + 2) (by omega)
    have h1 := omega_eq_gamma k hk
    rw [h2, h1]
    have harg : (((k + 2 : ℕ) : ℝ) / 2 + 1) = ((k : ℝ) / 2 + 1) + 1 := by
      push_cast; ring
    rw [harg, Real.Gamma_add_one (by positivity : (k : ℝ) / 2 + 1 ≠ 0)]
    have hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi := by
      rw [Real.sq_sqrt Real.pi_nonneg]
    rw [pow_add, hpi]
    field_simp

/-! ## The slice integral as a cosine integral -/

/-- Change of variables `t = sin θ`: the slice integral is `∫_0^{π/2} cos^{m+1}`. -/
theorem sphereSlice_eq_cos (m : ℕ) :
    sphereSlice m = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ ^ (m + 1) := by
  have h1 : sphereSlice m = ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ ((m : ℝ) / 2) := by
    rw [sphereSlice]
    have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (f := fun s => (1 - s ^ 2) ^ ((m : ℝ) / 2))
    simp only [neg_zero] at hneg
    rw [← hneg]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    simp only [neg_sq]
  rw [h1]
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := Real.sin) (f' := Real.cos)
    (g := fun u => (1 - u ^ 2) ^ ((m : ℝ) / 2))
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
    ((Real.continuous_rpow_const (by positivity : (0:ℝ) ≤ (m:ℝ)/2)).comp (by fun_prop))
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hx
  have hcos0 : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by have := Real.pi_pos; linarith [hx.1], hx.2⟩
  change (1 - Real.sin x ^ 2) ^ ((m : ℝ) / 2) * Real.cos x = Real.cos x ^ (m + 1)
  have hcos_sq : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
    rw [Real.sin_sq]; ring
  have hbase : Real.cos x ^ 2 = (Real.cos x) ^ (2 : ℝ) := (Real.rpow_natCast (Real.cos x) 2).symm
  have h2 : (Real.cos x ^ 2) ^ ((m : ℝ) / 2) = Real.cos x ^ m := by
    rw [hbase, ← Real.rpow_mul hcos0]
    rw [show (2 : ℝ) * ((m : ℝ) / 2) = m by ring]
    rw [Real.rpow_natCast]
  rw [hcos_sq, h2, pow_succ]

/-- The slice integral at `m = 0` is `1`. -/
theorem sphereSlice_zero : sphereSlice 0 = 1 := by
  rw [sphereSlice]
  simp only [Nat.cast_zero, zero_div, Real.rpow_zero]
  rw [intervalIntegral.integral_const]
  norm_num

/-- The slice integral at `m = 1` is `π/4`. -/
theorem sphereSlice_one : sphereSlice 1 = Real.pi / 4 := by
  rw [sphereSlice_eq_cos]
  rw [integral_cos_sq]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  ring

/-- Two-step recurrence `sphereSlice (m+2) = ((m+2)/(m+3)) sphereSlice m`. -/
theorem sphereSlice_rec (m : ℕ) :
    sphereSlice (m + 2) = ((m : ℝ) + 2) / ((m : ℝ) + 3) * sphereSlice m := by
  rw [sphereSlice_eq_cos, sphereSlice_eq_cos]
  have h := integral_cos_pow (a := (0:ℝ)) (b := Real.pi / 2) (n := m + 1)
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero] at h
  have hb2 : (0:ℝ) ^ (m + 1 + 1) * 1 - 1 ^ (m + 1 + 1) * 0 = 0 := by
    rw [zero_pow (by omega), mul_one, one_pow, mul_zero, sub_zero]
  have hb3 : ((0:ℝ) ^ (m + 1 + 1) * 1 - 1 ^ (m + 1 + 1) * 0) /
      (((m+1:ℕ):ℝ) + 2) = 0 := by
    rw [hb2, zero_div]
  rw [hb3, zero_add] at h
  rw [show m + 2 + 1 = m + 1 + 2 by omega]
  rw [h]
  push_cast
  ring

/-! ## The sphere-slicing identity -/

/-- **Sphere slicing.**  `ω_{m+1} = 2 ω_m ∫_{-1}^0 (1-s²)^{m/2} ds` for every `m`. -/
theorem sphereSlicingTarget (m : ℕ) : SphereSlicingTarget m := by
  unfold SphereSlicingTarget
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [omega_zero, sphereSlice_zero, omega_one]
    norm_num
  | one =>
    rw [omega_two, omega_one, sphereSlice_one]
    ring
  | more n ih1 ih2 =>
    have hrec2 := omega_rec n
    have hrec3 := omega_rec (n + 1)
    have hs := sphereSlice_rec n
    rw [show n + 2 + 1 = n + 3 by omega]
    rw [hrec3, hrec2, hs, ih1]
    field_simp
    push_cast
    ring

/-! ## Consequences for the hemisphere -/

/-- **Hemisphere volume.**  `|C| = ω_{m+1}/2`. -/
theorem hemisphere_revolutionVolume_eq (m : ℕ) :
    (hemisphere m).revolutionVolume = omega (m + 1) / 2 :=
  hemisphere_revolutionVolume_eq_of_slicing m (sphereSlicingTarget m)

/-- The manuscript's hemisphere-volume target. -/
theorem hemisphere_volume_target (m : ℕ) : HemisphereVolumeTarget m :=
  hemisphere_volume_target_of_slicing m (sphereSlicingTarget m)

/-- The slice integral equals the power integral of the semicircular profile. -/
theorem semi_pow_integral (j : ℕ) :
    ∫ s in (-1 : ℝ)..0, (semi 1 s) ^ j = sphereSlice j := by
  have h := hemisphere_revolutionVolume_eq_slice j
  simp only [hemisphere, revolutionVolume] at h
  exact mul_left_cancel₀ (omega_ne_zero j) h

/-- The lateral-area integrand of the hemisphere collapses to `(semi 1 s)^{m-2}`. -/
theorem hemisphere_lateral_eq (m : ℕ) (hm : 2 ≤ m) :
    (hemisphere m).lateralArea = (m : ℝ) * omega m * sphereSlice (m - 2) := by
  simp only [hemisphere, lateralArea]
  congr 1
  rw [← semi_pow_integral (m - 2)]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
  have hpos : 0 < 1 - (s + 1) ^ 2 := by nlinarith [hs.1, hs.2]
  have hsemi_pos : 0 < semi 1 s := semi_pos 1 (le_refl 1) ⟨hs.1, hs.2⟩
  have hderiv : deriv (semi 1) s = semiD 1 s := deriv_semi 1 hpos
  have hsqrt : Real.sqrt (1 + (deriv (semi 1) s) ^ 2) = 1 / semi 1 s := by
    rw [hderiv]
    have hmain : 1 + (semiD 1 s) ^ 2 = (1 / semi 1 s) ^ 2 := by
      simp only [semiD, semi]
      field_simp
      rw [Real.sq_sqrt hpos.le]
      ring
    rw [hmain, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hcollapse : (semi 1 s) ^ (m - 1) * (1 / semi 1 s) = (semi 1 s) ^ (m - 2) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ, div_eq_mul_inv,
      mul_assoc, one_mul, mul_inv_cancel₀ (ne_of_gt hsemi_pos), mul_one]
  rw [hsqrt, hcollapse]

/-- **Hemisphere area.**  `|Γ| = (m+1) ω_{m+1}/2` for `m ≥ 1`. -/
theorem hemisphere_revolutionArea_eq (m : ℕ) (hm : 1 ≤ m) :
    (hemisphere m).revolutionArea = ((m : ℝ) + 1) * omega (m + 1) / 2 := by
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · rw [← hm1, hemisphere_one_revolutionArea, omega_two]
    norm_num
  · have hT := sphereSlicingTarget m
    unfold SphereSlicingTarget at hT
    have hlat := hemisphere_lateral_eq m (by omega)
    have hterm : (hemisphere m).terminalArea = 0 := by
      simp only [hemisphere, terminalArea]
      have h0 : semi 1 0 = 0 := by simp [semi]
      rw [h0, zero_pow (by omega : m ≠ 0), mul_zero]
    rw [revolutionArea, hlat, hterm, add_zero]
    have hsrec := sphereSlice_rec (m - 2)
    have hnum : (((m - 2 : ℕ)) : ℝ) + 2 = (m : ℝ) := by
      exact_mod_cast (show (m - 2 : ℕ) + 2 = m by omega)
    have hden : (((m - 2 : ℕ)) : ℝ) + 3 = (m : ℝ) + 1 := by
      exact_mod_cast (show (m - 2 : ℕ) + 3 = m + 1 by omega)
    have hcoef : (((m - 2 : ℕ) : ℝ) + 2) / (((m - 2 : ℕ) : ℝ) + 3) =
        (m : ℝ) / ((m : ℝ) + 1) := by
      rw [hnum, hden]
    rw [hcoef] at hsrec
    rw [show m - 2 + 2 = m by omega] at hsrec
    rw [hT, hsrec]
    field_simp

/-- **Hemisphere functional.**  `𝓕 = ω_{m+1}/2` for `m ≥ 1`. -/
theorem hemisphere_revolutionF_eq (m : ℕ) (hm : 1 ≤ m) :
    (hemisphere m).revolutionF = omega (m + 1) / 2 := by
  rw [revolutionF, hemisphere_revolutionArea_eq m hm, hemisphere_revolutionVolume_eq]
  ring

end

end Cap
end RobinCaps
