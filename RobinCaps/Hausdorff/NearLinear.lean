import RobinCaps.Hausdorff.AreaIface

/-!
# Near-linear comparison of Hausdorff measure (wave 12, Problem A: `NearLinearProp`)

This file proves `nearLinear_hnl`, which is exactly the statement `NearLinearProp m k` from
`RobinCaps.Hausdorff.AreaIface`: if `F : E_m → E_k` is uniformly `ε`-close to a linear map
`A : E_m →L[ℝ] E_k` on a set `S` (in the sense `‖F x - F y - A (x - y)‖ ≤ ε ‖x - y‖`), and
`A` expands norms by at least `σ > 0` (`σ ‖v‖ ≤ ‖A v‖`), with `0 ≤ ε < σ`, then the Hausdorff
`m`-measures of `F '' S` and `A '' S` are comparable:

  `((σ - ε)/σ)^m • μH[m] (A '' S) ≤ μH[m] (F '' S) ≤ ((σ + ε)/σ)^m • μH[m] (A '' S)`.

## Strategy

* `A` is automatically injective (since `σ > 0`).
* For `x, y ∈ S`, the triangle inequality and the two hypotheses give
  `‖F x - F y‖ ≤ ‖A x - A y‖ + ε ‖x - y‖` and `‖A x - A y‖ ≤ ‖F x - F y‖ + ε ‖x - y‖`.
* Combining the first inequality with `σ ‖x - y‖ ≤ ‖A x - A y‖` yields the *multiplicative*
  inequality `σ ‖F x - F y‖ ≤ (σ + ε) ‖A x - A y‖`, i.e. `F` composed with a partial inverse of
  `A` is `((σ+ε)/σ)`-Lipschitz on `A '' S`, with image exactly `F '' S`.
  `LipschitzOnWith.hausdorffMeasure_image_le` then gives the upper bound.
* Symmetrically, `(σ - ε) ‖x - y‖ ≤ ‖F x - F y‖` shows `F` is injective on `S`, and combined with
  the second inequality gives `(σ - ε) ‖A x - A y‖ ≤ σ ‖F x - F y‖`, i.e. `A` composed with a
  partial inverse of `F` is `(σ/(σ-ε))`-Lipschitz on `F '' S`, with image exactly `A '' S`.
  This yields `μH[m] (A '' S) ≤ (σ/(σ-ε))^m • μH[m] (F '' S)`; multiplying both sides by
  `((σ-ε)/σ)^m` (using `((σ-ε)/σ) * (σ/(σ-ε)) = 1`) produces the lower bound.

No hypothesis is left open: the theorem is proved in full from the interface statement.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace RobinCaps.Hausdorff

theorem nearLinear_hnl (m k : ℕ) : NearLinearProp m k := by
  intro F A σ ε hσ hε0 hεσ hA S hF
  haveI : Nonempty (EuclideanSpace ℝ (Fin m)) := ⟨0⟩
  -- Trivial case: `S` is empty.
  rcases eq_empty_or_nonempty S with hSe | -
  · subst hSe
    simp
  -- From here on we do not actually need nonemptiness of `S`, all arguments below are
  -- vacuously true (or trivially true) when `S = ∅`, but we keep the case split above for
  -- clarity; the rest of the proof works uniformly.
  · -- `A` is injective since `σ > 0`.
    have hAinj : Function.Injective A := by
      intro x y hxy
      have h0 : ‖A (x - y)‖ = 0 := by simp [map_sub, hxy]
      have hle : σ * ‖x - y‖ ≤ ‖A (x - y)‖ := hA (x - y)
      rw [h0] at hle
      have hz : ‖x - y‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
      have hxy0 : x - y = 0 := by rwa [norm_eq_zero] at hz
      exact sub_eq_zero.mp hxy0
    -- Basic expansion estimate for `A`, without any subtraction.
    have hAxy : ∀ x y : EuclideanSpace ℝ (Fin m), σ * ‖x - y‖ ≤ ‖A x - A y‖ := by
      intro x y
      have h := hA (x - y)
      rwa [map_sub] at h
    -- `‖F x - F y‖ ≤ ‖A x - A y‖ + ε ‖x - y‖` on `S`.
    have hkey : ∀ x ∈ S, ∀ y ∈ S, ‖F x - F y‖ ≤ ‖A x - A y‖ + ε * ‖x - y‖ := by
      intro x hx y hy
      have h1 := hF x hx y hy
      have h2 : F x - F y = A (x - y) + (F x - F y - A (x - y)) := by abel
      calc
        ‖F x - F y‖ = ‖A (x - y) + (F x - F y - A (x - y))‖ := by rw [← h2]
        _ ≤ ‖A (x - y)‖ + ‖F x - F y - A (x - y)‖ := norm_add_le _ _
        _ ≤ ‖A (x - y)‖ + ε * ‖x - y‖ := by linarith
        _ = ‖A x - A y‖ + ε * ‖x - y‖ := by rw [map_sub]
    -- `‖A x - A y‖ ≤ ‖F x - F y‖ + ε ‖x - y‖` on `S`.
    have h5 : ∀ x ∈ S, ∀ y ∈ S, ‖A x - A y‖ ≤ ‖F x - F y‖ + ε * ‖x - y‖ := by
      intro x hx y hy
      have h1 := hF x hx y hy
      have heq : A (x - y) = (F x - F y) - (F x - F y - A (x - y)) := by abel
      calc
        ‖A x - A y‖ = ‖A (x - y)‖ := by rw [map_sub]
        _ = ‖(F x - F y) - (F x - F y - A (x - y))‖ := congrArg norm heq
        _ ≤ ‖F x - F y‖ + ‖F x - F y - A (x - y)‖ := norm_sub_le _ _
        _ ≤ ‖F x - F y‖ + ε * ‖x - y‖ := by linarith
    -- Multiplicative upper bound: `σ ‖F x - F y‖ ≤ (σ + ε) ‖A x - A y‖`.
    have hUBmul : ∀ x ∈ S, ∀ y ∈ S, σ * ‖F x - F y‖ ≤ (σ + ε) * ‖A x - A y‖ := by
      intro x hx y hy
      have h1 := hkey x hx y hy
      have h2 := hAxy x y
      nlinarith [mul_le_mul_of_nonneg_left h1 hσ.le, mul_le_mul_of_nonneg_left h2 hε0]
    -- Division form: `‖F x - F y‖ ≤ ((σ+ε)/σ) ‖A x - A y‖`.
    have hUB : ∀ x ∈ S, ∀ y ∈ S, ‖F x - F y‖ ≤ (σ + ε) / σ * ‖A x - A y‖ := by
      intro x hx y hy
      rw [div_mul_eq_mul_div, le_div_iff₀ hσ, mul_comm ‖F x - F y‖ σ]
      exact hUBmul x hx y hy
    -- Lower bound: `(σ - ε) ‖x - y‖ ≤ ‖F x - F y‖` on `S`; in particular `F` is injective on `S`.
    have hLB1 : ∀ x ∈ S, ∀ y ∈ S, (σ - ε) * ‖x - y‖ ≤ ‖F x - F y‖ := by
      intro x hx y hy
      have h1 := hF x hx y hy
      have h2 := hAxy x y
      have h3 : ‖A x - A y‖ = ‖A (x - y)‖ := by rw [map_sub]
      have hrev : ‖A (x - y)‖ - ‖F x - F y‖ ≤ ‖A (x - y) - (F x - F y)‖ := norm_sub_norm_le _ _
      have heq : A (x - y) - (F x - F y) = -(F x - F y - A (x - y)) := by abel
      have hbound : ‖A (x - y) - (F x - F y)‖ ≤ ε * ‖x - y‖ := by
        rw [heq, norm_neg]; exact h1
      linarith
    have hσεpos : 0 < σ - ε := by linarith
    have hFinj : Set.InjOn F S := by
      intro a ha b hb hab
      have h1 := hLB1 a ha b hb
      have h2 : ‖F a - F b‖ = 0 := by rw [hab]; simp
      rw [h2] at h1
      have hz : ‖a - b‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
      have hab0 : a - b = 0 := by rwa [norm_eq_zero] at hz
      exact sub_eq_zero.mp hab0
    -- Multiplicative lower bound: `(σ - ε) ‖A x - A y‖ ≤ σ ‖F x - F y‖`.
    have hLBmul : ∀ x ∈ S, ∀ y ∈ S, (σ - ε) * ‖A x - A y‖ ≤ σ * ‖F x - F y‖ := by
      intro x hx y hy
      have h1 := h5 x hx y hy
      have h2 := hLB1 x hx y hy
      nlinarith [mul_le_mul_of_nonneg_left h1 hσεpos.le, mul_le_mul_of_nonneg_left h2 hε0]
    -- Division form: `‖A x - A y‖ ≤ (σ/(σ-ε)) ‖F x - F y‖`.
    have hLBc : ∀ x ∈ S, ∀ y ∈ S, ‖A x - A y‖ ≤ σ / (σ - ε) * ‖F x - F y‖ := by
      intro x hx y hy
      rw [div_mul_eq_mul_div, le_div_iff₀ hσεpos, mul_comm ‖A x - A y‖ (σ - ε)]
      exact hLBmul x hx y hy
    -- Partial inverses of `A` and `F` on `S`.
    have hinvA : ∀ a ∈ S, Function.invFunOn A S (A a) = a := fun a ha =>
      hAinj (Function.invFunOn_apply_eq ha)
    have hinvF : ∀ a ∈ S, Function.invFunOn F S (F a) = a := fun a ha =>
      hFinj (Function.invFunOn_apply_mem ha) ha (Function.invFunOn_apply_eq ha)
    ------------------------------------------------------------------
    -- Upper bound: μH[m] (F '' S) ≤ ((σ+ε)/σ)^m * μH[m] (A '' S)
    ------------------------------------------------------------------
    have hG_lip :
        LipschitzOnWith (((σ + ε) / σ)).toNNReal (F ∘ Function.invFunOn A S) (A '' S) := by
      apply LipschitzOnWith.of_dist_le'
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [Function.comp_apply]
      rw [hinvA a ha, hinvA b hb, dist_eq_norm, dist_eq_norm]
      exact hUB a ha b hb
    have hG_image : (F ∘ Function.invFunOn A S) '' (A '' S) = F '' S := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        simp only [Function.comp_apply, hinvA a ha]
        exact ⟨a, ha, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨A a, ⟨a, ha, rfl⟩, by simp [Function.comp_apply, hinvA a ha]⟩
    have hub_measure :
        (Measure.hausdorffMeasure (m : ℝ)) ((F ∘ Function.invFunOn A S) '' (A '' S))
          ≤ (((σ + ε) / σ).toNNReal : ℝ≥0∞) ^ (m : ℝ)
              * (Measure.hausdorffMeasure (m : ℝ)) (A '' S) :=
      hG_lip.hausdorffMeasure_image_le (Nat.cast_nonneg m)
    rw [hG_image] at hub_measure
    have hc1nonneg : (0:ℝ) ≤ (σ + ε) / σ := by positivity
    have hconv1 :
        (((σ + ε) / σ).toNNReal : ℝ≥0∞) ^ (m : ℝ) = ENNReal.ofReal (((σ + ε) / σ) ^ m) := by
      show ENNReal.ofReal ((σ + ε) / σ) ^ (m : ℝ) = ENNReal.ofReal (((σ + ε) / σ) ^ m)
      rw [ENNReal.ofReal_rpow_of_nonneg hc1nonneg (Nat.cast_nonneg m), Real.rpow_natCast]
    rw [hconv1] at hub_measure
    have hUB_final :
        (Measure.hausdorffMeasure (m : ℝ)) (F '' S)
          ≤ ENNReal.ofReal (((σ + ε) / σ) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (A '' S) :=
      hub_measure
    ------------------------------------------------------------------
    -- Lower bound: ((σ-ε)/σ)^m * μH[m] (A '' S) ≤ μH[m] (F '' S)
    ------------------------------------------------------------------
    have hH_lip :
        LipschitzOnWith ((σ / (σ - ε))).toNNReal (A ∘ Function.invFunOn F S) (F '' S) := by
      apply LipschitzOnWith.of_dist_le'
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [Function.comp_apply]
      rw [hinvF a ha, hinvF b hb, dist_eq_norm, dist_eq_norm]
      exact hLBc a ha b hb
    have hH_image : (A ∘ Function.invFunOn F S) '' (F '' S) = A '' S := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        simp only [Function.comp_apply, hinvF a ha]
        exact ⟨a, ha, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨F a, ⟨a, ha, rfl⟩, by simp [Function.comp_apply, hinvF a ha]⟩
    have hlb_measure :
        (Measure.hausdorffMeasure (m : ℝ)) ((A ∘ Function.invFunOn F S) '' (F '' S))
          ≤ ((σ / (σ - ε)).toNNReal : ℝ≥0∞) ^ (m : ℝ)
              * (Measure.hausdorffMeasure (m : ℝ)) (F '' S) :=
      hH_lip.hausdorffMeasure_image_le (Nat.cast_nonneg m)
    rw [hH_image] at hlb_measure
    have hc2nonneg : (0:ℝ) ≤ σ / (σ - ε) := by positivity
    have hconv2 :
        ((σ / (σ - ε)).toNNReal : ℝ≥0∞) ^ (m : ℝ) = ENNReal.ofReal ((σ / (σ - ε)) ^ m) := by
      show ENNReal.ofReal (σ / (σ - ε)) ^ (m : ℝ) = ENNReal.ofReal ((σ / (σ - ε)) ^ m)
      rw [ENNReal.ofReal_rpow_of_nonneg hc2nonneg (Nat.cast_nonneg m), Real.rpow_natCast]
    rw [hconv2] at hlb_measure
    have hlb_measure' :
        (Measure.hausdorffMeasure (m : ℝ)) (A '' S)
          ≤ ENNReal.ofReal ((σ / (σ - ε)) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (F '' S) :=
      hlb_measure
    have hc0nonneg : (0:ℝ) ≤ (σ - ε) / σ := by positivity
    have hc0c2 : (σ - ε) / σ * (σ / (σ - ε)) = 1 := by
      rw [div_mul_div_comm, mul_comm (σ - ε) σ]
      exact div_self (mul_ne_zero hσ.ne' hσεpos.ne')
    have hcombine :
        ENNReal.ofReal (((σ - ε) / σ) ^ m) * ENNReal.ofReal ((σ / (σ - ε)) ^ m) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((σ - ε) / σ) ^ m), ← mul_pow, hc0c2,
        one_pow, ENNReal.ofReal_one]
    have hstep :
        ENNReal.ofReal (((σ - ε) / σ) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (A '' S)
          ≤ ENNReal.ofReal (((σ - ε) / σ) ^ m)
              * (ENNReal.ofReal ((σ / (σ - ε)) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (F '' S)) := by
      gcongr
    have hLB_final :
        ENNReal.ofReal (((σ - ε) / σ) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (A '' S)
          ≤ (Measure.hausdorffMeasure (m : ℝ)) (F '' S) := by
      calc
        ENNReal.ofReal (((σ - ε) / σ) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (A '' S)
            ≤ ENNReal.ofReal (((σ - ε) / σ) ^ m)
                * (ENNReal.ofReal ((σ / (σ - ε)) ^ m)
                    * (Measure.hausdorffMeasure (m : ℝ)) (F '' S)) := hstep
        _ = (ENNReal.ofReal (((σ - ε) / σ) ^ m) * ENNReal.ofReal ((σ / (σ - ε)) ^ m))
              * (Measure.hausdorffMeasure (m : ℝ)) (F '' S) := by rw [mul_assoc]
        _ = 1 * (Measure.hausdorffMeasure (m : ℝ)) (F '' S) := by rw [hcombine]
        _ = (Measure.hausdorffMeasure (m : ℝ)) (F '' S) := one_mul _
    exact ⟨hLB_final, hUB_final⟩

end RobinCaps.Hausdorff

end
