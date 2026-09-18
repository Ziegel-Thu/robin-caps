import Mathlib

/-!
# Algebraic lemmas about symmetric bilinear forms

This file collects purely algebraic facts about symmetric bilinear forms
`Q N : W →ₗ[ℝ] W →ₗ[ℝ] ℝ` on a real vector space `W`: basic expansion identities
(binomial expansions on sums, differences and scalar multiples, the parallelogram
identity), the minimising-sequence estimate and the first-variation lemma used to
identify extremals of a Rayleigh quotient `Q / N`, and the Cauchy-Schwarz inequality
for a nonnegative symmetric bilinear form.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.Compact

variable {W : Type*} [AddCommGroup W] [Module ℝ W] {Q N : W →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/-- Expansion of a symmetric bilinear form on a sum. -/
theorem bilin_add_add (hQ : ∀ u v, Q u v = Q v u) (u v : W) :
    Q (u + v) (u + v) = Q u u + 2 * Q u v + Q v v := by
  simp only [map_add, LinearMap.add_apply]
  rw [hQ v u]
  ring

/-- Expansion of a symmetric bilinear form on a difference. -/
theorem bilin_sub_sub (hQ : ∀ u v, Q u v = Q v u) (u v : W) :
    Q (u - v) (u - v) = Q u u - 2 * Q u v + Q v v := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [hQ v u]
  ring

/-- Expansion of a symmetric bilinear form on a scalar multiple. -/
theorem bilin_smul_smul (c : ℝ) (u : W) : Q (c • u) (c • u) = c ^ 2 * Q u u := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Parallelogram identity. -/
theorem bilin_parallelogram (hQ : ∀ u v, Q u v = Q v u) (u v : W) :
    Q (u - v) (u - v) + Q (u + v) (u + v) = 2 * Q u u + 2 * Q v v := by
  rw [bilin_sub_sub hQ, bilin_add_add hQ]
  ring

/-- Expansion of a symmetric bilinear form on `u + t • v`, for a real scalar `t`. -/
theorem bilin_add_smul_smul (hQ : ∀ u v, Q u v = Q v u) (u v : W) (t : ℝ) :
    Q (u + t • v) (u + t • v) = Q u u + 2 * t * Q u v + t ^ 2 * Q v v := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hQ v u]
  ring

/-- **The minimising-sequence estimate.** If `Q ≥ lam • N` everywhere
(`hlow : ∀ w, lam * N w w ≤ Q w w`), then for all `u v`:
`Q (u - v) (u - v) ≤ 2 * Q u u + 2 * Q v v - lam * (2 * N u u + 2 * N v v - N (u - v) (u - v))`. -/
theorem bilin_sub_le_of_lower (hQ : ∀ u v, Q u v = Q v u) (hN : ∀ u v, N u v = N v u)
    (lam : ℝ) (hlow : ∀ w, lam * N w w ≤ Q w w) (u v : W) :
    Q (u - v) (u - v) ≤
      2 * Q u u + 2 * Q v v - lam * (2 * N u u + 2 * N v v - N (u - v) (u - v)) := by
  have hp := bilin_parallelogram hQ u v
  have hpN := bilin_parallelogram hN u v
  have hl := hlow (u + v)
  have key : lam * N (u + v) (u + v) = lam * (2 * N u u + 2 * N v v - N (u - v) (u - v)) := by
    have hN' : N (u + v) (u + v) = 2 * N u u + 2 * N v v - N (u - v) (u - v) := by linarith
    rw [hN']
  linarith [hp, hl, key]

/-- **First variation.** If `ψ` attains the lower bound (`Q ψ ψ = lam * N ψ ψ`) and
`lam * N w w ≤ Q w w` for all `w`, then `Q ψ v = lam * N ψ v` for every `v`. -/
theorem bilin_eq_of_isMin (hQ : ∀ u v, Q u v = Q v u) (hN : ∀ u v, N u v = N v u)
    (lam : ℝ) (hlow : ∀ w, lam * N w w ≤ Q w w) (ψ : W)
    (hψ : Q ψ ψ = lam * N ψ ψ) (v : W) : Q ψ v = lam * N ψ v := by
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * (Q ψ v - lam * N ψ v) + t ^ 2 * (Q v v - lam * N v v) := by
    intro t
    have hQe := bilin_add_smul_smul hQ ψ v t
    have hNe := bilin_add_smul_smul hN ψ v t
    have hl := hlow (ψ + t • v)
    rw [hQe, hNe, hψ] at hl
    nlinarith [hl]
  have hb : 0 ≤ Q v v - lam * N v v := by linarith [hlow v]
  set a := Q ψ v - lam * N ψ v with ha_def
  set b := Q v v - lam * N v v with hb_def
  have hb1pos : 0 < b + 1 := by linarith [hb]
  have ht := hquad (-a / (b + 1))
  have ht' : 0 ≤ (2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b) * (b + 1) ^ 2 :=
    mul_nonneg ht (le_of_lt (pow_pos hb1pos 2))
  have hbne : (b + 1) ≠ 0 := ne_of_gt hb1pos
  have heq : (2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b) * (b + 1) ^ 2
      = a ^ 2 * (-(b + 2)) := by
    field_simp
    ring
  rw [heq] at ht'
  have ha2le : a ^ 2 ≤ 0 := by nlinarith [ht', hb]
  have ha2 : a ^ 2 = 0 := le_antisymm ha2le (sq_nonneg a)
  have ha0 : a = 0 := by
    have := sq_eq_zero_iff.mp ha2
    exact this
  linarith [ha0, ha_def]

/-- A nonnegative symmetric bilinear form satisfies Cauchy–Schwarz. -/
theorem bilin_cauchy_schwarz (hN : ∀ u v, N u v = N v u) (hpos : ∀ w, 0 ≤ N w w) (u v : W) :
    N u v ^ 2 ≤ N u u * N v v := by
  rcases eq_or_lt_of_le (hpos v) with hv0 | hvpos
  · -- `N v v = 0`
    have hv0' : N v v = 0 := hv0.symm
    have hlin : ∀ t : ℝ, 0 ≤ N u u + 2 * t * N u v := by
      intro t
      have he := bilin_add_smul_smul hN u v t
      have hp := hpos (u + t • v)
      rw [he, hv0'] at hp
      nlinarith [hp]
    have huv0 : N u v = 0 := by
      by_contra hne
      have h2 : (2 : ℝ) * N u v ≠ 0 := mul_ne_zero two_ne_zero hne
      have hlt := hlin (-(N u u + 1) / (2 * N u v))
      have heqt : N u u + 2 * (-(N u u + 1) / (2 * N u v)) * N u v = -1 := by
        field_simp
        ring
      rw [heqt] at hlt
      linarith
    rw [huv0, hv0']
    norm_num
  · -- `N v v > 0`
    have he := bilin_add_smul_smul hN u v (-(N u v) / N v v)
    have hp := hpos (u + (-(N u v) / N v v) • v)
    rw [he] at hp
    have hnv : N v v ≠ 0 := ne_of_gt hvpos
    have key : N u u + 2 * (-(N u v) / N v v) * N u v + (-(N u v) / N v v) ^ 2 * N v v
        = N u u - N u v ^ 2 / N v v := by
      field_simp
      ring
    rw [key] at hp
    have h1 : (N u u - N u v ^ 2 / N v v) * N v v ≥ 0 := mul_nonneg hp (le_of_lt hvpos)
    have h2 : (N u u - N u v ^ 2 / N v v) * N v v = N u u * N v v - N u v ^ 2 := by
      field_simp
    linarith [h1, h2]

end RobinCaps.Compact
