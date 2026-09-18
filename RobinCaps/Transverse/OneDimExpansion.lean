import RobinCaps.Transverse.OneDimBall
import RobinCaps.Transverse.GroundStateOne

/-!
# The transverse ground state in dimension `m = 1`: `eq:Psi-H1` and `eq:d-R`

Discharges the two remaining quantitative statements of Lemma 4.1
(`lem:transverse`) of `reference/robin_endcaps_corrected_en.tex` for transverse
dimension `m = 1`, recorded as the targets `PsiH1Target` and `dRTarget` in
`RobinCaps.Transverse.OneDimBall`:

* `psiH1_target` : `eq:Psi-H1`, `‖Ψ_R - ω₁^{-1/2}‖_{H¹(-1,1)} ≤ C R`;
* `dR_target`    : `eq:d-R`, `|d_R - √ω₁| ≤ C R²` and `d_R ≥ ½ √ω₁`.

## The mechanism

Writing `k = k₁(α,α;2R)` and `κ_R = R k`, the phase equation `2Rk = 2 arctan(α/k)`
says exactly `arctan (α/k) = κ_R`, so the ground profile
`x ↦ cos(k x - arctan(α/k))` transplanted by `x = R (z+1)` is the *even* profile
`z ↦ cos (κ_R z)` on `(-1,1)` (`groundProfile_scaled`).  Consequently

* `κ_R² ≤ α R` and `α R - (α R)²/2 ≤ κ_R²` (`kappa_sq_le`, `kappa_sq_ge`),
  a sharpening of `nuR_expansion` since `κ_R² = R² ν_R` (`kappa_sq_eq`);
* `Ψ_R (z) = cos (κ_R z) / √(1 + sin κ_R cos κ_R / κ_R)` (`scaledGroundState_eq`),
  and `Ψ_R(z) = √R ψ_R(R z)` for the ground state `psiN` of `GroundStateOne`
  (`psiN_scaled_eq`);
* the squared `H¹` distance to the constant `2^{-1/2}` is `≤ 4 κ_R⁴ = O(R²)`
  (`h1_kappa_bound`), the `L²` and Dirichlet parts being `O(κ_R⁴)` separately;
* `d_R = 2 sin κ_R / (κ_R √(cosMass κ_R))` obeys `|d_R - √2| ≤ 2 κ_R⁴`
  (`dR_kappa_bound`).  The exponent `R²` (rather than `R`) of `eq:d-R` rests on
  the sixth-order cancellation
  `|2 sin²κ - κ² - κ sin κ cos κ| ≤ κ⁶` (`sinCos_sixth_bound`),
  which is proved from a Taylor ladder for `sin` and `cos`
  (`sub_cube_div_six_le_sin`, `cos_le_quartic`, `sin_le_quintic`,
  `sextic_le_cos`) obtained by four successive monotonicity arguments on
  `[0, ∞)`.
-/

namespace RobinCaps.Transverse

noncomputable section

/-! ### A Taylor ladder for `sin` and `cos` on `[0, ∞)` -/

private lemma monoOn_Ici {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : ∀ x : ℝ, 0 < x → 0 ≤ deriv f x) : MonotoneOn f (Set.Ici (0 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
    hf.differentiableOn ?_
  intro x hx
  rw [interior_Ici] at hx
  exact hf' x hx

private lemma hasDerivAt_quartic (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24) (-t + t ^ 3 / 6) t := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24)
      (0 - (2 : ℕ) * t ^ (2 - 1) / 2 + (4 : ℕ) * t ^ (4 - 1) / 24) t :=
    (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
      ((hasDerivAt_pow 4 t).div_const 24))
  convert h1 using 1
  push_cast
  ring

/-- `x - x³/6 ≤ sin x` for `x ≥ 0`. -/
theorem sub_cube_div_six_le_sin {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hmono : Monotone fun t : ℝ => Real.sin t - (t - t ^ 3 / 6) := by
    refine monotone_of_deriv_nonneg ?_ ?_
    · fun_prop
    · intro t
      have hd : HasDerivAt (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6))
          (Real.cos t - (1 - t ^ 2 / 2)) t := by
        have h1 : HasDerivAt (fun s : ℝ => s - s ^ 3 / 6)
            (1 - (3 : ℕ) * t ^ (3 - 1) / 6) t :=
          (hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)
        have h2 : (1 : ℝ) - (3 : ℕ) * t ^ (3 - 1) / 6 = 1 - t ^ 2 / 2 := by
          push_cast; ring
        rw [h2] at h1
        exact (Real.hasDerivAt_sin t).sub h1
      rw [hd.deriv]
      linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have h := hmono hx
  simp only [Real.sin_zero] at h
  norm_num at h
  linarith

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for `x ≥ 0`. -/
theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hmono : MonotoneOn (fun t : ℝ => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
      (Set.Ici (0 : ℝ)) := by
    refine monoOn_Ici (by fun_prop) ?_
    intro t ht
    have hd : HasDerivAt (fun s : ℝ => (1 - s ^ 2 / 2 + s ^ 4 / 24) - Real.cos s)
        ((-t + t ^ 3 / 6) - -Real.sin t) t :=
      (hasDerivAt_quartic t).sub (Real.hasDerivAt_cos t)
    rw [hd.deriv]
    linarith [sub_cube_div_six_le_sin ht.le]
  have h := hmono Set.left_mem_Ici hx hx
  simp only [Real.cos_zero] at h
  norm_num at h
  linarith

/-- `sin x ≤ x - x³/6 + x⁵/120` for `x ≥ 0`. -/
theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hmono : MonotoneOn (fun t : ℝ => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
      (Set.Ici (0 : ℝ)) := by
    refine monoOn_Ici (by fun_prop) ?_
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 120)
        (1 - (3 : ℕ) * t ^ (3 - 1) / 6 + (5 : ℕ) * t ^ (5 - 1) / 120) t :=
      ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)
    have h2 : (1 : ℝ) - (3 : ℕ) * t ^ (3 - 1) / 6 + (5 : ℕ) * t ^ (5 - 1) / 120
        = 1 - t ^ 2 / 2 + t ^ 4 / 24 := by push_cast; ring
    rw [h2] at h1
    have hd : HasDerivAt (fun s : ℝ => (s - s ^ 3 / 6 + s ^ 5 / 120) - Real.sin s)
        ((1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t) t := h1.sub (Real.hasDerivAt_sin t)
    rw [hd.deriv]
    linarith [cos_le_quartic ht.le]
  have h := hmono Set.left_mem_Ici hx hx
  simp only [Real.sin_zero] at h
  norm_num at h
  linarith

/-- `1 - x²/2 + x⁴/24 - x⁶/720 ≤ cos x` for `x ≥ 0`. -/
theorem sextic_le_cos {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hmono : MonotoneOn
      (fun t : ℝ => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (Set.Ici (0 : ℝ)) := by
    refine monoOn_Ici (by fun_prop) ?_
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)
        ((-t + t ^ 3 / 6) - (6 : ℕ) * t ^ (6 - 1) / 720) t :=
      (hasDerivAt_quartic t).sub ((hasDerivAt_pow 6 t).div_const 720)
    have h2 : ((-t + t ^ 3 / 6) - (6 : ℕ) * t ^ (6 - 1) / 720)
        = -(t - t ^ 3 / 6 + t ^ 5 / 120) := by push_cast; ring
    rw [h2] at h1
    have hd : HasDerivAt (fun s : ℝ =>
        Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
        (-Real.sin t - -(t - t ^ 3 / 6 + t ^ 5 / 120)) t :=
      (Real.hasDerivAt_cos t).sub h1
    rw [hd.deriv]
    linarith [sin_le_quintic ht.le]
  have h := hmono Set.left_mem_Ici hx hx
  simp only [Real.cos_zero] at h
  norm_num at h
  linarith

/-! ### The sixth-order cancellation `2 sin²κ - κ² - κ sin κ cos κ = O(κ⁶)` -/

/-- `|1 - cos w - w²/4 - w sin w / 4| ≤ w⁶/480` for `w ≥ 0`. -/
theorem phase_sixth_bound {w : ℝ} (hw : 0 ≤ w) :
    |1 - Real.cos w - w ^ 2 / 4 - w * Real.sin w / 4| ≤ w ^ 6 / 480 := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hc := cos_le_quartic hw
    have hws : w * Real.sin w ≤ w * (w - w ^ 3 / 6 + w ^ 5 / 120) :=
      mul_le_mul_of_nonneg_left (sin_le_quintic hw) hw
    nlinarith [hc, hws]
  · have hc := sextic_le_cos hw
    have hws : w * (w - w ^ 3 / 6) ≤ w * Real.sin w :=
      mul_le_mul_of_nonneg_left (sub_cube_div_six_le_sin hw) hw
    nlinarith [hc, hws, pow_nonneg hw 6]

/-- The sixth-order cancellation behind `eq:d-R`:
`|2 sin²κ - κ² - κ sin κ cos κ| ≤ κ⁶` for `κ ≥ 0`. -/
theorem sinCos_sixth_bound {κ : ℝ} (hκ : 0 ≤ κ) :
    |2 * Real.sin κ ^ 2 - κ ^ 2 - κ * (Real.sin κ * Real.cos κ)| ≤ κ ^ 6 := by
  have h := phase_sixth_bound (w := 2 * κ) (by linarith)
  have hcos : Real.cos (2 * κ) = 1 - 2 * Real.sin κ ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq κ]
  have hsin : Real.sin (2 * κ) = 2 * Real.sin κ * Real.cos κ := Real.sin_two_mul κ
  rw [hcos, hsin] at h
  have e : 2 * Real.sin κ ^ 2 - κ ^ 2 - κ * (Real.sin κ * Real.cos κ)
      = 1 - (1 - 2 * Real.sin κ ^ 2) - (2 * κ) ^ 2 / 4
        - (2 * κ) * (2 * Real.sin κ * Real.cos κ) / 4 := by ring
  rw [e]
  refine h.trans ?_
  nlinarith [pow_nonneg hκ 6]

/-! ### The three elementary integrals on `(-1, 1)` -/

/-- `∫_{-1}^{1} cos(κ z)² dz = 1 + sin κ cos κ / κ`. -/
theorem integral_cos_mul_sq {κ : ℝ} (hκ : κ ≠ 0) :
    (∫ z in (-1 : ℝ)..1, Real.cos (κ * z) ^ 2) = 1 + Real.sin κ * Real.cos κ / κ := by
  rw [intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (f := fun x : ℝ => Real.cos x ^ 2) hκ, integral_cos_sq]
  simp only [mul_one, mul_neg_one, Real.cos_neg, Real.sin_neg, smul_eq_mul]
  field_simp
  ring

/-- `∫_{-1}^{1} sin(κ z)² dz = 1 - sin κ cos κ / κ`. -/
theorem integral_sin_mul_sq {κ : ℝ} (hκ : κ ≠ 0) :
    (∫ z in (-1 : ℝ)..1, Real.sin (κ * z) ^ 2) = 1 - Real.sin κ * Real.cos κ / κ := by
  rw [intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (f := fun x : ℝ => Real.sin x ^ 2) hκ, integral_sin_sq]
  simp only [mul_one, mul_neg_one, Real.cos_neg, Real.sin_neg, smul_eq_mul]
  field_simp
  ring

/-- `∫_{-1}^{1} cos(κ z) dz = 2 sin κ / κ`. -/
theorem integral_cos_mul {κ : ℝ} (hκ : κ ≠ 0) :
    (∫ z in (-1 : ℝ)..1, Real.cos (κ * z)) = 2 * Real.sin κ / κ := by
  rw [intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (f := fun x : ℝ => Real.cos x) hκ, integral_cos]
  simp only [mul_one, mul_neg_one, Real.sin_neg, smul_eq_mul]
  field_simp
  ring

/-! ### The normalising mass `∫_{-1}^{1} cos²(κ z) dz` -/

/-- The squared `L²(-1,1)` norm of the rescaled profile `z ↦ cos (κ z)`. -/
def cosMass (κ : ℝ) : ℝ := 1 + Real.sin κ * Real.cos κ / κ

/-- `2 - (2/3) κ² ≤ ∫_{-1}^{1} cos²(κ z) dz ≤ 2`. -/
theorem cosMass_bounds {κ : ℝ} (hκ : 0 < κ) :
    2 - 2 * κ ^ 2 / 3 ≤ cosMass κ ∧ cosMass κ ≤ 2 := by
  have hdouble : Real.sin κ * Real.cos κ = Real.sin (2 * κ) / 2 := by
    rw [Real.sin_two_mul]; ring
  have hup : Real.sin (2 * κ) ≤ 2 * κ := (Real.sin_lt (by linarith)).le
  have hlow : 2 * κ - (2 * κ) ^ 3 / 6 ≤ Real.sin (2 * κ) :=
    sub_cube_div_six_le_sin (by linarith)
  constructor
  · have h1 : (1 - 2 * κ ^ 2 / 3) * κ ≤ Real.sin κ * Real.cos κ := by
      rw [hdouble]; nlinarith [hlow]
    have h2 := (le_div_iff₀ hκ).mpr h1
    simp only [cosMass]
    linarith
  · have h1 : Real.sin κ * Real.cos κ ≤ 1 * κ := by rw [hdouble]; nlinarith [hup]
    have h2 := (div_le_iff₀ hκ).mpr h1
    simp only [cosMass]
    linarith

/-- `κ * (∫_{-1}^{1} cos²(κ z) dz) = κ + sin κ cos κ`. -/
theorem mul_cosMass {κ : ℝ} (hκ : κ ≠ 0) :
    κ * cosMass κ = κ + Real.sin κ * Real.cos κ := by
  simp only [cosMass]
  field_simp

/-- The derivative of the rescaled profile. -/
theorem deriv_cos_mul_div (κ N z : ℝ) :
    deriv (fun y : ℝ => Real.cos (κ * y) / N) z = -Real.sin (κ * z) * κ / N := by
  have h1 : HasDerivAt (fun y : ℝ => κ * y) κ z := by
    simpa using (hasDerivAt_id z).const_mul κ
  exact ((h1.cos).div_const N).deriv

/-! ### The two quantitative estimates, in terms of `κ` -/

/-- The `L²` part of `eq:Psi-H1`, with the normalising constants abstracted. -/
private lemma L2_core {κ N s : ℝ} (hκ : 0 < κ) (_hκ1 : κ ≤ 1)
    (hN1 : 1 ≤ N) (hNs : N ≤ s) (hs15 : s ≤ 3 / 2) (hsN : s - N ≤ κ ^ 2 / 3) :
    (∫ z in (-1 : ℝ)..1, (Real.cos (κ * z) / N - s⁻¹) ^ 2) ≤ 25 / 18 * κ ^ 4 := by
  have hspos : (0 : ℝ) < s := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hNs1 : (1 : ℝ) ≤ N * s := by nlinarith
  have hκ2 : (0 : ℝ) ≤ κ ^ 2 := sq_nonneg κ
  have hmono : (∫ z in (-1 : ℝ)..1, (Real.cos (κ * z) / N - s⁻¹) ^ 2)
      ≤ ∫ _z in (-1 : ℝ)..1, (5 / 6 * κ ^ 2) ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro z hz
    have hz2 : z ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
    have hX1 : Real.cos (κ * z) ≤ 1 := Real.cos_le_one _
    have hX2 : 1 - (κ * z) ^ 2 / 2 ≤ Real.cos (κ * z) := Real.one_sub_sq_div_two_le_cos
    have hX2' : 1 - κ ^ 2 / 2 ≤ Real.cos (κ * z) := by nlinarith
    have h1 : s * (1 - κ ^ 2 / 2) ≤ s * Real.cos (κ * z) :=
      mul_le_mul_of_nonneg_left hX2' hspos.le
    have h2 : s * Real.cos (κ * z) ≤ s * 1 := mul_le_mul_of_nonneg_left hX1 hspos.le
    have h3 : (5 / 6 * κ ^ 2) * 1 ≤ (5 / 6 * κ ^ 2) * (N * s) :=
      mul_le_mul_of_nonneg_left hNs1 (by positivity)
    have h4 : s * (κ ^ 2 / 2) ≤ (3 / 2) * (κ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hs15 (by positivity)
    have he : Real.cos (κ * z) / N - s⁻¹ = (s * Real.cos (κ * z) - N) / (N * s) := by
      field_simp
    rw [he]
    refine sq_le_sq' ?_ ?_
    · rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
  have hconst : (∫ _z in (-1 : ℝ)..1, (5 / 6 * κ ^ 2) ^ 2) = 2 * (5 / 6 * κ ^ 2) ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  rw [hconst] at hmono
  nlinarith [hmono]

/-- The Dirichlet part of `eq:Psi-H1`, with the normalising constant abstracted. -/
private lemma Dir_core {κ N : ℝ} (hκ : 0 < κ) (hN1 : 1 ≤ N) :
    (∫ z in (-1 : ℝ)..1, deriv (fun y : ℝ => Real.cos (κ * y) / N) z ^ 2)
      ≤ 2 * κ ^ 4 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
  have hmono : (∫ z in (-1 : ℝ)..1, deriv (fun y : ℝ => Real.cos (κ * y) / N) z ^ 2)
      ≤ ∫ _z in (-1 : ℝ)..1, κ ^ 4 := by
    simp only [deriv_cos_mul_div]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    intro z hz
    have hz2 : z ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
    have hsin : Real.sin (κ * z) ^ 2 ≤ (κ * z) ^ 2 := Real.sin_sq_le_sq
    have hsin' : Real.sin (κ * z) ^ 2 ≤ κ ^ 2 := by nlinarith [sq_nonneg κ]
    have he : (-Real.sin (κ * z) * κ / N) ^ 2
        = Real.sin (κ * z) ^ 2 * κ ^ 2 / N ^ 2 := by
      field_simp
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg κ, pow_nonneg hκ.le 4, sq_nonneg (Real.sin (κ * z))]
  have hconst : (∫ _z in (-1 : ℝ)..1, κ ^ 4) = 2 * κ ^ 4 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  rw [hconst] at hmono
  exact hmono

/-- Elementary facts about the normalising constant `N = √(cosMass κ)`. -/
private lemma norm_facts {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (1 : ℝ) ≤ Real.sqrt (cosMass κ) ∧ Real.sqrt (cosMass κ) ≤ Real.sqrt 2 ∧
      Real.sqrt 2 ≤ 3 / 2 ∧ 1.4 ≤ Real.sqrt 2 ∧
      Real.sqrt 2 - Real.sqrt (cosMass κ) ≤ κ ^ 2 / 3 ∧
      Real.sqrt (cosMass κ) ^ 2 = cosMass κ := by
  obtain ⟨hQl, hQu⟩ := cosMass_bounds hκ
  have hκ2 : κ ^ 2 ≤ 1 := by nlinarith
  have hQpos : 0 < cosMass κ := by nlinarith
  have hN2 : Real.sqrt (cosMass κ) ^ 2 = cosMass κ := Real.sq_sqrt hQpos.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hNpos : 0 < Real.sqrt (cosMass κ) := Real.sqrt_pos.mpr hQpos
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hN1 : (1 : ℝ) ≤ Real.sqrt (cosMass κ) := by nlinarith
  have hs14 : 1.4 ≤ Real.sqrt 2 := by nlinarith
  have hs15 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have hNs : Real.sqrt (cosMass κ) ≤ Real.sqrt 2 := by nlinarith
  have h24 : (2 : ℝ) ≤ Real.sqrt 2 + Real.sqrt (cosMass κ) := by linarith
  have hprod : (Real.sqrt 2 - Real.sqrt (cosMass κ)) *
      (Real.sqrt 2 + Real.sqrt (cosMass κ)) ≤ 2 / 3 * κ ^ 2 := by nlinarith
  have hsub : (0 : ℝ) ≤ Real.sqrt 2 - Real.sqrt (cosMass κ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left h24 hsub
  exact ⟨hN1, hNs, hs15, hs14, by linarith, hN2⟩

/-- **`eq:Psi-H1` at the level of `κ`**: the squared `H¹(-1,1)` distance from the
normalised profile `cos(κ ·)/‖cos(κ ·)‖` to the constant `2^{-1/2}` is `O(κ⁴)`. -/
theorem h1_kappa_bound {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫ z in (-1 : ℝ)..1,
        (Real.cos (κ * z) / Real.sqrt (cosMass κ) - (Real.sqrt 2)⁻¹) ^ 2)
      + (∫ z in (-1 : ℝ)..1,
        deriv (fun y : ℝ => Real.cos (κ * y) / Real.sqrt (cosMass κ)) z ^ 2)
      ≤ 4 * κ ^ 4 := by
  obtain ⟨hN1, hNs, hs15, -, hsN, -⟩ := norm_facts hκ hκ1
  have h1 := L2_core (κ := κ) (N := Real.sqrt (cosMass κ)) (s := Real.sqrt 2)
    hκ hκ1 hN1 hNs hs15 hsN
  have h2 := Dir_core (κ := κ) (N := Real.sqrt (cosMass κ)) hκ hN1
  linarith [pow_nonneg hκ.le 4]

/-- **`eq:d-R` at the level of `κ`**: the mean of the normalised profile is
`√2 + O(κ⁴)`. -/
theorem dR_kappa_bound {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    |(∫ z in (-1 : ℝ)..1, Real.cos (κ * z) / Real.sqrt (cosMass κ)) - Real.sqrt 2|
      ≤ 2 * κ ^ 4 := by
  obtain ⟨hQl, hQu⟩ := cosMass_bounds hκ
  obtain ⟨hN1, hNs, hs15, hs14, hsN, hN2⟩ := norm_facts hκ hκ1
  have hκ2 : κ ^ 2 ≤ 1 := by nlinarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsinpos : 0 < Real.sin κ := by
    refine Real.sin_pos_of_pos_of_lt_pi hκ ?_
    linarith [Real.pi_gt_three]
  have hint : (∫ z in (-1 : ℝ)..1, Real.cos (κ * z) / Real.sqrt (cosMass κ))
      = 2 * Real.sin κ / κ / Real.sqrt (cosMass κ) := by
    rw [intervalIntegral.integral_div, integral_cos_mul (ne_of_gt hκ)]
  rw [hint]
  set N := Real.sqrt (cosMass κ) with hNdef
  set s := Real.sqrt 2 with hsdef
  clear_value N s
  clear hNdef hsdef
  set Q := cosMass κ with hQdef
  have hQκ : κ * Q = κ + Real.sin κ * Real.cos κ := mul_cosMass (ne_of_gt hκ)
  clear_value Q
  clear hQdef
  have hNpos : (0 : ℝ) < N := by linarith
  have hd : (0 : ℝ) < 2 * Real.sin κ / κ / N := by positivity
  set d := 2 * Real.sin κ / κ / N with hddef
  have hd2 : d ^ 2 * (κ ^ 2 * Q) = 4 * Real.sin κ ^ 2 := by
    rw [hddef, ← hN2]
    field_simp
    ring
  clear_value d
  clear hddef
  set P := 2 * Real.sin κ ^ 2 - κ ^ 2 - κ * (Real.sin κ * Real.cos κ) with hPdef
  have hP : |P| ≤ κ ^ 6 := sinCos_sixth_bound hκ.le
  have hκ2pos : (0 : ℝ) < κ ^ 2 := pow_pos hκ 2
  have hQ43' : (4 : ℝ) / 3 ≤ Q := by linarith
  have hQ43 : 4 / 3 * κ ^ 2 ≤ κ ^ 2 * Q := by
    have := mul_le_mul_of_nonneg_left hQ43' (le_of_lt hκ2pos)
    linarith
  have hQpos : (0 : ℝ) < κ ^ 2 * Q := by linarith
  have hdiff : (d ^ 2 - 2) * (κ ^ 2 * Q) = 2 * P := by
    rw [hPdef]; linear_combination hd2 + (-2 * κ) * hQκ
  have habs : |d ^ 2 - 2| * (κ ^ 2 * Q) = 2 * |P| := by
    rw [← abs_of_pos hQpos, ← abs_mul, hdiff, abs_mul]
    norm_num
  have hmul1 : |d ^ 2 - 2| * (4 / 3 * κ ^ 2) ≤ |d ^ 2 - 2| * (κ ^ 2 * Q) :=
    mul_le_mul_of_nonneg_left hQ43 (abs_nonneg _)
  have hstep : |d ^ 2 - 2| * (4 / 3 * κ ^ 2) ≤ 3 / 2 * κ ^ 4 * (4 / 3 * κ ^ 2) := by
    have hrw : 3 / 2 * κ ^ 4 * (4 / 3 * κ ^ 2) = 2 * κ ^ 6 := by ring
    rw [hrw]
    linarith [hmul1, habs, hP]
  have hsq : |d ^ 2 - 2| ≤ 3 / 2 * κ ^ 4 :=
    le_of_mul_le_mul_right hstep (by linarith)
  have hfac : |d - s| * (d + s) = |d ^ 2 - 2| := by
    have h1 : (0 : ℝ) ≤ d + s := by linarith
    rw [← abs_of_nonneg h1, ← abs_mul]
    congr 1
    linear_combination -hs2
  have hds : (1.4 : ℝ) ≤ d + s := by linarith
  have h7 : |d - s| * 1.4 ≤ |d - s| * (d + s) :=
    mul_le_mul_of_nonneg_left hds (abs_nonneg _)
  linarith [h7, hfac, hsq, pow_nonneg hκ.le 4]

/-! ### The rescaled frequency `κ_R = R k₁(α, α; 2R)` -/

/-- `κ_R = R k₁(α,α;2R)`: the transverse ground-state frequency after rescaling
`B_1(R) = (-R,R)` to `B_1(1) = (-1,1)`.  One has `κ_R² = R² ν_R`. -/
def kappa (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  R * Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1)

theorem kappa_def (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    kappa α R hα hR
      = R * Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1) := rfl

theorem kappa_pos (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : 0 < kappa α R hα hR :=
  mul_pos hR (Interval.phaseRoot_pos α α (2 * R) 1 hα hα (by positivity) (le_refl 1))

/-- `κ_R² = R² ν_R`: the rescaled frequency squared is the rescaled eigenvalue. -/
theorem kappa_sq_eq (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    kappa α R hα hR ^ 2 = R ^ 2 * nuR α R hα hR := by
  rw [kappa_def]
  simp only [nuR, Interval.mu]
  ring

/-- **The phase equation for `ℓ = 2R`**: `arctan (α / k₁) = κ_R`. -/
theorem arctan_eq_kappa (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    Real.arctan (α / Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1))
      = kappa α R hα hR := by
  have h := Interval.phaseRoot_eq α α (2 * R) 1 hα hα (by positivity) (le_refl 1)
  simp only [Interval.phaseFun, Nat.cast_one, sub_self, zero_mul, sub_zero] at h
  rw [kappa_def]
  linarith

/-- The phase argument rewritten through `κ_R`: `α / k₁ = α R / κ_R`. -/
theorem alpha_div_phaseRoot (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    α / Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1)
      = α * R / kappa α R hα hR := by
  rw [kappa_def]
  have hk : Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1) ≠ 0 :=
    ne_of_gt (Interval.phaseRoot_pos α α (2 * R) 1 hα hα (by positivity) (le_refl 1))
  field_simp

/-- **`κ_R² ≤ α R`** (equivalently `R² ν_R ≤ α R`): the upper half of
`eq:nu-expansion`, in the sharp form supplied by `arctan x ≤ x`. -/
theorem kappa_sq_le (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    kappa α R hα hR ^ 2 ≤ α * R := by
  have hκ := kappa_pos α R hα hR
  have h1 := arctan_eq_kappa α R hα hR
  rw [alpha_div_phaseRoot α R hα hR] at h1
  have h2 : Real.arctan (α * R / kappa α R hα hR) ≤ α * R / kappa α R hα hR :=
    arctan_le_self (by positivity)
  rw [h1, le_div_iff₀ hκ] at h2
  nlinarith [h2]

/-- **Crude lower bound `(2/3) α R ≤ κ_R²`** for `α R ≤ 1/2`. -/
theorem kappa_sq_ge_two_thirds (α R : ℝ) (hα : 0 < α) (hR : 0 < R)
    (hAR : α * R ≤ 1 / 2) : 2 / 3 * (α * R) ≤ kappa α R hα hR ^ 2 := by
  have hκ := kappa_pos α R hα hR
  have h1 := arctan_eq_kappa α R hα hR
  rw [alpha_div_phaseRoot α R hα hR] at h1
  have hle := kappa_sq_le α R hα hR
  -- `κ ≤ π/4` because `κ² ≤ αR ≤ 1/2`
  have hπ : (0.75 : ℝ) < Real.pi / 4 := by linarith [Real.pi_gt_three]
  have hκsmall : kappa α R hα hR < Real.pi / 4 := by nlinarith
  -- hence `x := αR/κ ≤ 1`
  have hx1 : α * R / kappa α R hα hR ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Real.arctan_mono hcon.le
    rw [h1, Real.arctan_one] at this
    linarith
  have hxpos : 0 < α * R / kappa α R hα hR := by positivity
  have h2 : α * R / kappa α R hα hR - (α * R / kappa α R hα hR) ^ 3 / 3
      ≤ Real.arctan (α * R / kappa α R hα hR) := sub_cube_le_arctan hxpos.le
  rw [h1] at h2
  have hx2 : (α * R / kappa α R hα hR) ^ 2 ≤ 1 := by nlinarith [hxpos, hx1]
  have h3 : (α * R / kappa α R hα hR) ^ 3 ≤ α * R / kappa α R hα hR := by
    linarith [mul_le_mul_of_nonneg_left hx2 hxpos.le]
  have h4 : 2 / 3 * (α * R / kappa α R hα hR) ≤ kappa α R hα hR := by linarith
  have h5 := mul_le_mul_of_nonneg_right h4 hκ.le
  have h6 : 2 / 3 * (α * R / kappa α R hα hR) * kappa α R hα hR = 2 / 3 * (α * R) := by
    field_simp
  rw [h6] at h5
  nlinarith [h5]

/-- **`eq:nu-expansion`, lower half, in sharp form**: `α R - (α R)²/2 ≤ κ_R²`
for `α R ≤ 1/2`. -/
theorem kappa_sq_ge (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (hAR : α * R ≤ 1 / 2) :
    α * R - (α * R) ^ 2 / 2 ≤ kappa α R hα hR ^ 2 := by
  have hκ := kappa_pos α R hα hR
  have hARpos : 0 < α * R := by positivity
  have h1 := arctan_eq_kappa α R hα hR
  rw [alpha_div_phaseRoot α R hα hR] at h1
  have hcrude := kappa_sq_ge_two_thirds α R hα hR hAR
  have hxpos : 0 < α * R / kappa α R hα hR := by positivity
  have h2 : α * R / kappa α R hα hR - (α * R / kappa α R hα hR) ^ 3 / 3
      ≤ Real.arctan (α * R / kappa α R hα hR) := sub_cube_le_arctan hxpos.le
  rw [h1] at h2
  have h5 := mul_le_mul_of_nonneg_right h2 hκ.le
  have h6 : (α * R / kappa α R hα hR - (α * R / kappa α R hα hR) ^ 3 / 3)
      * kappa α R hα hR
      = α * R - (α * R) ^ 3 / (3 * kappa α R hα hR ^ 2) := by
    field_simp
  rw [h6] at h5
  have h7 : (α * R) ^ 3 / (3 * kappa α R hα hR ^ 2) ≤ (α * R) ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hcrude, hARpos]
  linarith

/-! ### The rescaled ground state is `cos (κ_R ·)`, normalised -/

/-- The transverse profile, transplanted to `(-1,1)`, is `z ↦ cos (κ_R z)`. -/
theorem groundProfile_scaled (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (z : ℝ) :
    groundProfile α R hα hR (R * (z + 1)) = Real.cos (kappa α R hα hR * z) := by
  simp only [groundProfile]
  rw [arctan_eq_kappa α R hα hR, kappa_def]
  congr 1
  ring

/-- The normalising factor of `eq:scaled-groundstate` is `√(∫_{-1}^{1} cos²(κ_R z) dz)`. -/
theorem scaledNorm_eq (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    scaledNorm α R hα hR = Real.sqrt (cosMass (kappa α R hα hR)) := by
  simp only [scaledNorm, groundProfile_scaled]
  rw [integral_cos_mul_sq (ne_of_gt (kappa_pos α R hα hR))]
  simp only [cosMass]

/-- `Ψ_R (z) = cos(κ_R z) / ‖cos (κ_R ·)‖_{L²(-1,1)}`. -/
theorem scaledGroundState_eq (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    scaledGroundState α R hα hR
      = fun z : ℝ =>
        Real.cos (kappa α R hα hR * z) / Real.sqrt (cosMass (kappa α R hα hR)) := by
  funext z
  simp only [scaledGroundState, groundProfile_scaled, scaledNorm_eq]

/-! ### Relation to the ground state of `RobinCaps.Transverse.GroundStateOne` -/

/-- The profile used in `GroundStateOne` is the profile used in `OneDimBall`. -/
theorem gpFun_eq_groundProfile (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    gpFun α R hα hR = groundProfile α R hα hR := rfl

/-- **Change of variables `x = R (z + 1)`**: the `L²(B_1(R))` mass of the
unnormalised ground state is `R` times the squared normalising factor of `Ψ_R`. -/
theorem psi1_mass_eq_scaledNorm_sq (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    Sobolev.Weak.mass (psi1 α R hα hR) = R * scaledNorm α R hα hR ^ 2 := by
  have hnn : 0 ≤ ∫ z in (-1 : ℝ)..1, groundProfile α R hα hR (R * (z + 1)) ^ 2 := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u _
    positivity
  have hsq : scaledNorm α R hα hR ^ 2
      = ∫ z in (-1 : ℝ)..1, groundProfile α R hα hR (R * (z + 1)) ^ 2 := by
    simp only [scaledNorm]
    exact Real.sq_sqrt hnn
  have h := intervalIntegral.integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
      (f := fun x : ℝ => groundProfile α R hα hR x ^ 2) (ne_of_gt hR) R
  simp only [smul_eq_mul] at h
  have e1 : R * (-1) + R = 0 := by ring
  have e2 : R * 1 + R = 2 * R := by ring
  rw [e1, e2] at h
  rw [psi1_mass, hsq, gpFun_eq_groundProfile]
  simp only [mul_add, mul_one]
  rw [h]
  field_simp

theorem scaledNorm_pos (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : 0 < scaledNorm α R hα hR := by
  have hm := psi1_mass_pos α R hα hR
  rw [psi1_mass_eq_scaledNorm_sq α R hα hR] at hm
  have h3 : 0 ≤ scaledNorm α R hα hR := by
    simp only [scaledNorm]
    exact Real.sqrt_nonneg _
  rcases lt_or_eq_of_le h3 with h | h
  · exact h
  · rw [← h] at hm
    norm_num at hm

/-- **`eq:scaled-groundstate` for `m = 1`**: `Ψ_R(z) = R^{1/2} ψ_R(R z)`, where
`ψ_R = psiN` is the `L²`-normalised transverse ground state on `B_1(R)`. -/
theorem psiN_scaled_eq (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (z : ℝ) :
    scaledGroundState α R hα hR z
      = Real.sqrt R * (psiN α R hα hR).toFun (ept (R * z)) := by
  have hN := scaledNorm_pos α R hα hR
  have hRs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsqrt : Real.sqrt (Sobolev.Weak.mass (psi1 α R hα hR))
      = Real.sqrt R * scaledNorm α R hα hR := by
    rw [psi1_mass_eq_scaledNorm_sq α R hα hR, Real.sqrt_mul hR.le, Real.sqrt_sq hN.le]
  simp only [psiN, Sobolev.Weak.H1.smul_toFun, Pi.smul_apply, smul_eq_mul, psi1_toFun,
    psiFun_ept, hsqrt, scaledGroundState, gpFun_eq_groundProfile]
  rw [show R * z + R = R * (z + 1) by ring]
  field_simp

/-! ### The two targets of `lem:transverse` for `m = 1` -/

private lemma kappa_small (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (hR0 : R < 1 / (2 * α)) :
    0 < kappa α R hα hR ∧ kappa α R hα hR ≤ 1 ∧
      kappa α R hα hR ^ 4 ≤ (α * R) ^ 2 ∧ α * R < 1 / 2 := by
  have hκ := kappa_pos α R hα hR
  have hAR : α * R < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * α)] at hR0
    nlinarith
  have hle := kappa_sq_le α R hα hR
  refine ⟨hκ, by nlinarith, ?_, hAR⟩
  have : kappa α R hα hR ^ 4 = (kappa α R hα hR ^ 2) ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg (kappa α R hα hR), hle]

/-- **`eq:Psi-H1` for `m = 1`**: the target `PsiH1Target` of `OneDimBall`. -/
theorem psiH1_target (α : ℝ) (hα : 0 < α) : PsiH1Target α hα := by
  refine ⟨2 * α, 1 / (2 * α), by positivity, ?_⟩
  intro R hR hR0
  obtain ⟨hκ, hκ1, hκ4, -⟩ := kappa_small α R hα hR hR0
  rw [scaledGroundState_eq α R hα hR]
  have h := h1_kappa_bound hκ hκ1
  calc (∫ z in (-1 : ℝ)..1,
        (Real.cos (kappa α R hα hR * z) / Real.sqrt (cosMass (kappa α R hα hR))
          - (Real.sqrt 2)⁻¹) ^ 2)
      + (∫ z in (-1 : ℝ)..1,
        deriv (fun y : ℝ =>
          Real.cos (kappa α R hα hR * y) / Real.sqrt (cosMass (kappa α R hα hR))) z ^ 2)
      ≤ 4 * kappa α R hα hR ^ 4 := h
    _ ≤ (2 * α) ^ 2 * R ^ 2 := by nlinarith [hκ4]

/-- **`eq:d-R` for `m = 1`**: the target `dRTarget` of `OneDimBall`. -/
theorem dR_target (α : ℝ) (hα : 0 < α) : dRTarget α hα := by
  refine ⟨2 * α ^ 2, 1 / (2 * α), by positivity, ?_⟩
  intro R hR hR0
  obtain ⟨hκ, hκ1, hκ4, hAR⟩ := kappa_small α R hα hR hR0
  have hARpos : 0 < α * R := by positivity
  have hdR : dR α R hα hR
      = ∫ z in (-1 : ℝ)..1,
        Real.cos (kappa α R hα hR * z) / Real.sqrt (cosMass (kappa α R hα hR)) := by
    simp only [dR, scaledGroundState_eq]
  have h := dR_kappa_bound hκ hκ1
  rw [← hdR] at h
  have hs14 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg 2]
  have hs15 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg 2]
  have habs := abs_le.mp h
  refine ⟨?_, ?_⟩
  · calc |dR α R hα hR - Real.sqrt 2| ≤ 2 * kappa α R hα hR ^ 4 := h
      _ ≤ 2 * α ^ 2 * R ^ 2 := by nlinarith [hκ4]
  · have hsmall : 2 * kappa α R hα hR ^ 4 ≤ 1 / 2 := by nlinarith [hκ4, hARpos]
    linarith [habs.1]

end

end RobinCaps.Transverse

