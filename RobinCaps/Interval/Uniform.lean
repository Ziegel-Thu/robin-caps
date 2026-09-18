import RobinCaps.Interval.Smooth

/-!
# Uniform perturbation bound for the interval Robin eigenvalues

This file makes the Lipschitz perturbation bound `mu_perturbation_bound` of
`RobinCaps.Interval.Smooth` uniform over the finitely many indices `1 ≤ j ≤ J`
(manuscript `eq:interval-O-R`: "uniformly over those indices").

* `mu_perturbation_bound_uniform`: a single constant `C ≥ 0` and a single radius `δ > 0`
  work for every `1 ≤ j ≤ J`.
* `mu_O_R`: if the perturbed parameters `pR R, qR R, ℓR R` are within `O(R)` of `p, q, L`,
  then `|μ_j(pR R, qR R; ℓR R) - μ_j(p, q; L)| ≤ C R` for all small `R > 0`,
  uniformly over `1 ≤ j ≤ J`.
-/

namespace RobinCaps.Interval

/-- Uniform version of `mu_perturbation_bound` over the indices `1 ≤ j ≤ J`. -/
theorem mu_perturbation_bound_uniform (J : ℕ) (p q L : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hL : 0 < L) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ j (hj : 1 ≤ j), j ≤ J →
      ∀ p' q' ℓ' : ℝ, |p' - p| ≤ δ → |q' - q| ≤ δ → |ℓ' - L| ≤ δ →
      ∀ (hp' : 0 < p') (hq' : 0 < q') (hℓ' : 0 < ℓ'),
        |mu p' q' ℓ' j hp' hq' hℓ' hj - mu p q L j hp hq hL hj|
          ≤ C * (|p' - p| + |q' - q| + |ℓ' - L|) := by
  induction J with
  | zero =>
    refine ⟨0, 1, le_rfl, one_pos, ?_⟩
    intro j hj hjJ
    omega
  | succ J ih =>
    obtain ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ := ih
    obtain ⟨C₂, δ₂, hδ₂, h₂⟩ :=
      mu_perturbation_bound (J + 1) (Nat.succ_le_succ (Nat.zero_le J)) p q L hp hq hL
    refine ⟨max C₁ C₂, min δ₁ δ₂, le_trans hC₁ (le_max_left _ _), lt_min hδ₁ hδ₂, ?_⟩
    intro j hj hjJ p' q' ℓ' hp'' hq'' hℓ'' hp' hq' hℓ'
    have hsum : 0 ≤ |p' - p| + |q' - q| + |ℓ' - L| := by positivity
    rcases Nat.lt_or_ge j (J + 1) with hlt | hge
    · have hjJ' : j ≤ J := Nat.lt_succ_iff.mp hlt
      have := h₁ j hj hjJ' p' q' ℓ' (le_trans hp'' (min_le_left _ _))
        (le_trans hq'' (min_le_left _ _)) (le_trans hℓ'' (min_le_left _ _)) hp' hq' hℓ'
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum)
    · have hjeq : j = J + 1 := le_antisymm hjJ hge
      subst hjeq
      have := h₂ p' q' ℓ' (le_trans hp'' (min_le_right _ _))
        (le_trans hq'' (min_le_right _ _)) (le_trans hℓ'' (min_le_right _ _)) hp' hq' hℓ'
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_right _ _) hsum)

/-- The `O(R)` form of the interval perturbation bound (`eq:interval-O-R`): if the perturbed
parameters are within `O(R)` of `(p, q, L)`, the interval eigenvalues are within `O(R)`,
uniformly over `1 ≤ j ≤ J`, for all sufficiently small `R > 0`. -/
theorem mu_O_R (J : ℕ) (p q L : ℝ) (hp : 0 < p) (hq : 0 < q) (hL : 0 < L)
    (pR qR ℓR : ℝ → ℝ) (Cp Cq Cℓ : ℝ)
    (hpR : ∀ R, 0 < R → |pR R - p| ≤ Cp * R)
    (hqR : ∀ R, 0 < R → |qR R - q| ≤ Cq * R)
    (hℓR : ∀ R, 0 < R → |ℓR R - L| ≤ Cℓ * R) :
    ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R, 0 < R → R < R₀ → ∀ j (hj : 1 ≤ j), j ≤ J →
      ∀ (hp' : 0 < pR R) (hq' : 0 < qR R) (hℓ' : 0 < ℓR R),
        |mu (pR R) (qR R) (ℓR R) j hp' hq' hℓ' hj - mu p q L j hp hq hL hj| ≤ C * R := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ := mu_perturbation_bound_uniform J p q L hp hq hL
  -- a common nonnegative Lipschitz constant for the three parameter perturbations
  set K : ℝ := max (max (max Cp Cq) Cℓ) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hCpK : Cp ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCqK : Cq ≤ K := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCℓK : Cℓ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨3 * C * K, δ / (K + 1), div_pos hδ hK1, ?_⟩
  intro R hR hRδ j hj hjJ hp' hq' hℓ'
  -- for `R < R₀` each parameter perturbation is at most `K R < δ`
  have hKR : K * R ≤ δ := by
    have : R * (K + 1) < δ := by
      rw [lt_div_iff₀ hK1] at hRδ
      exact hRδ
    nlinarith
  have hpδ : |pR R - p| ≤ δ :=
    le_trans (hpR R hR) (le_trans (mul_le_mul_of_nonneg_right hCpK hR.le) hKR)
  have hqδ : |qR R - q| ≤ δ :=
    le_trans (hqR R hR) (le_trans (mul_le_mul_of_nonneg_right hCqK hR.le) hKR)
  have hℓδ : |ℓR R - L| ≤ δ :=
    le_trans (hℓR R hR) (le_trans (mul_le_mul_of_nonneg_right hCℓK hR.le) hKR)
  have hmain := hbound j hj hjJ (pR R) (qR R) (ℓR R) hpδ hqδ hℓδ hp' hq' hℓ'
  have hsum : |pR R - p| + |qR R - q| + |ℓR R - L| ≤ 3 * K * R := by
    have h1 := le_trans (hpR R hR) (mul_le_mul_of_nonneg_right hCpK hR.le)
    have h2 := le_trans (hqR R hR) (mul_le_mul_of_nonneg_right hCqK hR.le)
    have h3 := le_trans (hℓR R hR) (mul_le_mul_of_nonneg_right hCℓK hR.le)
    linarith
  calc |mu (pR R) (qR R) (ℓR R) j hp' hq' hℓ' hj - mu p q L j hp hq hL hj|
      ≤ C * (|pR R - p| + |qR R - q| + |ℓR R - L|) := hmain
    _ ≤ C * (3 * K * R) := mul_le_mul_of_nonneg_left hsum hC
    _ = 3 * C * K * R := by ring

end RobinCaps.Interval
