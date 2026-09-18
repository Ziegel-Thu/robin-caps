import Mathlib

/-!
# Radial power series solution to the ODE

This file constructs the power series solution to the ODE `4 s g'' + 2 n g' + ν g = 0`
with initial condition `g(0) = 1`. The series
```
  g_ν(s) = ∑ a_k s^k
  a_0 = 1,  a_{k+1} = -ν a_k / (2 (k+1) (2k + n))
```
converges on all of ℝ and satisfies the ODE for all `s`. The coefficients satisfy the uniform
bound `|a_k| ≤ |ν|^k / (2^k k!)`, and the function is `C^∞` with explicit formulas for
derivatives.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.Compact

open Filter Topology

variable {n : ℕ} {ν : ℝ}

noncomputable section

/-- Coefficients: `a 0 = 1`, `a (k+1) = -ν * a k / (2 (k+1) (2 k + n))`. -/
def radCoeff (n : ℕ) (ν : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => -ν * radCoeff n ν k / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n))

theorem radCoeff_zero : radCoeff n ν 0 = 1 := rfl

theorem radCoeff_succ (k : ℕ) :
    radCoeff n ν (k + 1) = -ν * radCoeff n ν k / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n)) := rfl

/-- The recurrence relation: `2 (k+1) (2k + n) a_{k+1} + ν a_k = 0`. -/
theorem radCoeff_rec (hn : 1 ≤ n) (k : ℕ) :
    2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n) * radCoeff n ν (k + 1) + ν * radCoeff n ν k = 0 := by
  rw [radCoeff_succ]
  have h_pos : 0 < (2 : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + n) := by positivity
  field_simp
  ring

/-- Uniform bound on coefficients: `|a_k| ≤ |ν|^k / (2^k k!)`. -/
theorem abs_radCoeff_le (hn : 1 ≤ n) (k : ℕ) :
    |radCoeff n ν k| ≤ |ν| ^ k / (2 ^ k * k.factorial) := by
  induction k with
  | zero =>
    simp only [radCoeff_zero, Nat.factorial_zero, Nat.cast_one, pow_zero]
    norm_num
  | succ k ih =>
    rw [radCoeff_succ]
    have pos1 : 0 < (2 : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + n) := by positivity
    have hRHSdenom : (0 : ℝ) < 2 ^ (k + 1) * ((k + 1).factorial : ℝ) := by positivity
    have hLHSdenom : (0 : ℝ) < 2 ^ k * (k.factorial : ℝ) := by positivity
    have step_calc :
        |(-ν) * radCoeff n ν k / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n))| =
        |ν| * |radCoeff n ν k| / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n)) := by
      rw [abs_div, abs_of_pos pos1, abs_mul, abs_neg]
    rw [step_calc, div_le_div_iff₀ pos1 hRHSdenom]
    have ih' : |radCoeff n ν k| * (2 ^ k * (k.factorial : ℝ)) ≤ |ν| ^ k :=
      (le_div_iff₀ hLHSdenom).mp ih
    have factEq : (2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) =
        2 ^ k * (k.factorial : ℝ) * (2 * ((k : ℝ) + 1)) := by
      rw [pow_succ, Nat.factorial_succ]; push_cast; ring
    have key_denom : (2 : ℝ) * ((k : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n) := by
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    calc |ν| * |radCoeff n ν k| * (2 ^ (k + 1) * ((k + 1).factorial : ℝ))
        = |ν| * (|radCoeff n ν k| * (2 ^ k * (k.factorial : ℝ))) * (2 * ((k : ℝ) + 1)) := by
          rw [factEq]; ring
      _ ≤ |ν| * (|ν| ^ k) * (2 * ((k : ℝ) + 1)) := by
          gcongr
      _ = |ν| ^ (k + 1) * (2 * ((k : ℝ) + 1)) := by rw [pow_succ]; ring
      _ ≤ |ν| ^ (k + 1) * (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n)) := by
          gcongr

/-- Uniform bound on bounded sets: `|a_k s^k| ≤ (|ν| T / 2)^k / k!` for `|s| ≤ T`. -/
theorem abs_radCoeff_mul_pow_le (hn : 1 ≤ n) {s T : ℝ} (hs : |s| ≤ T) (k : ℕ) :
    |radCoeff n ν k * s ^ k| ≤ (|ν| * T / 2) ^ k / k.factorial := by
  rw [abs_mul, abs_pow]
  have hk : |radCoeff n ν k| ≤ |ν| ^ k / (2 ^ k * (k.factorial : ℝ)) := abs_radCoeff_le hn k
  have hpow : |s| ^ k ≤ T ^ k := pow_le_pow_left₀ (abs_nonneg s) hs k
  calc |radCoeff n ν k| * |s| ^ k
      ≤ (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * T ^ k :=
        mul_le_mul hk hpow (pow_nonneg (abs_nonneg s) k) (by positivity)
    _ = (|ν| * T / 2) ^ k / k.factorial := by
        rw [div_pow, mul_pow]; ring

/-- The power series `g_ν(s) = ∑ a_k s^k`. -/
def radSeries (n : ℕ) (ν : ℝ) (s : ℝ) : ℝ := ∑' k, radCoeff n ν k * s ^ k

/-- First derivative series `∑ (k+1) a_{k+1} s^k`. -/
def radSeries' (n : ℕ) (ν : ℝ) (s : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * radCoeff n ν (k + 1) * s ^ k

/-- Second derivative series `∑ (k+2)(k+1) a_{k+2} s^k`. -/
def radSeries'' (n : ℕ) (ν : ℝ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * radCoeff n ν (k + 2) * s ^ k

theorem summable_radSeries (hn : 1 ≤ n) (s : ℝ) :
    Summable fun k => radCoeff n ν k * s ^ k := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (|ν| * |s| / 2))
  intro idx
  have hbnd := abs_radCoeff_mul_pow_le (ν := ν) hn (le_refl |s|) idx
  simpa [Real.norm_eq_abs] using hbnd

theorem summable_radSeries' (hn : 1 ≤ n) (s : ℝ) :
    Summable fun k : ℕ => ((k : ℝ) + 1) * radCoeff n ν (k + 1) * s ^ k := by
  apply Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial (|ν| * |s| / 2)).mul_left (|ν| / 2))
  intro idx
  have hbnd : |radCoeff n ν (idx + 1)| ≤
      |ν| ^ (idx + 1) / (2 ^ (idx + 1) * ((idx + 1).factorial : ℝ)) := abs_radCoeff_le hn (idx + 1)
  have hnorm : ‖((idx : ℝ) + 1) * radCoeff n ν (idx + 1) * s ^ idx‖ =
      ((idx : ℝ) + 1) * |radCoeff n ν (idx + 1)| * |s| ^ idx := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (idx:ℝ) + 1),
      abs_pow]
  rw [hnorm]
  have step1 : ((idx : ℝ) + 1) * |radCoeff n ν (idx + 1)| * |s| ^ idx ≤
      ((idx : ℝ) + 1) * (|ν| ^ (idx + 1) / (2 ^ (idx + 1) * ((idx + 1).factorial : ℝ))) * |s| ^ idx :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbnd (by positivity)) (by positivity)
  have step2 : ((idx : ℝ) + 1) * (|ν| ^ (idx + 1) / (2 ^ (idx + 1) * ((idx + 1).factorial : ℝ))) *
      |s| ^ idx = |ν| / 2 * ((|ν| * |s| / 2) ^ idx / (idx.factorial : ℝ)) := by
    have hfact : ((idx + 1).factorial : ℝ) = ((idx : ℝ) + 1) * (idx.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hidx1 : ((idx : ℝ) + 1) ≠ 0 := by positivity
    have hfactne : (idx.factorial : ℝ) ≠ 0 := by positivity
    rw [hfact, pow_succ, div_pow, mul_pow]
    field_simp
    ring
  exact step2 ▸ step1

theorem summable_radSeries'' (hn : 1 ≤ n) (s : ℝ) :
    Summable fun k : ℕ => ((k : ℝ) + 2) * ((k : ℝ) + 1) * radCoeff n ν (k + 2) * s ^ k := by
  apply Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial (|ν| * |s| / 2)).mul_left ((|ν| / 2) ^ 2))
  intro idx
  have hbnd : |radCoeff n ν (idx + 2)| ≤
      |ν| ^ (idx + 2) / (2 ^ (idx + 2) * ((idx + 2).factorial : ℝ)) := abs_radCoeff_le hn (idx + 2)
  have hnorm : ‖((idx : ℝ) + 2) * ((idx : ℝ) + 1) * radCoeff n ν (idx + 2) * s ^ idx‖ =
      ((idx : ℝ) + 2) * ((idx : ℝ) + 1) * |radCoeff n ν (idx + 2)| * |s| ^ idx := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (idx:ℝ) + 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (idx:ℝ) + 1), abs_pow]
  rw [hnorm]
  have step1 : ((idx : ℝ) + 2) * ((idx : ℝ) + 1) * |radCoeff n ν (idx + 2)| * |s| ^ idx ≤
      ((idx : ℝ) + 2) * ((idx : ℝ) + 1) *
        (|ν| ^ (idx + 2) / (2 ^ (idx + 2) * ((idx + 2).factorial : ℝ))) * |s| ^ idx :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbnd (by positivity)) (by positivity)
  have step2 : ((idx : ℝ) + 2) * ((idx : ℝ) + 1) *
      (|ν| ^ (idx + 2) / (2 ^ (idx + 2) * ((idx + 2).factorial : ℝ))) * |s| ^ idx =
      (|ν| / 2) ^ 2 * ((|ν| * |s| / 2) ^ idx / (idx.factorial : ℝ)) := by
    have hfact : ((idx + 2).factorial : ℝ) =
        ((idx : ℝ) + 2) * ((idx : ℝ) + 1) * (idx.factorial : ℝ) := by
      rw [show idx + 2 = idx + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hidx2 : ((idx : ℝ) + 2) ≠ 0 := by positivity
    have hidx1 : ((idx : ℝ) + 1) ≠ 0 := by positivity
    have hfactne : (idx.factorial : ℝ) ≠ 0 := by positivity
    have h2pow : (2 : ℝ) ^ (idx + 2) = 2 ^ idx * 2 ^ 2 := by rw [pow_add]
    have hνpow : |ν| ^ (idx + 2) = |ν| ^ idx * |ν| ^ 2 := by rw [pow_add]
    have h2ne : (2 : ℝ) ^ idx ≠ 0 := by positivity
    rw [hfact, h2pow, hνpow, div_pow, div_pow, mul_pow]
    field_simp
  exact step2 ▸ step1

theorem radSeries_zero (hn : 1 ≤ n) : radSeries n ν 0 = 1 := by
  unfold radSeries
  have hsum : Summable fun k => radCoeff n ν k * (0:ℝ) ^ k := summable_radSeries hn 0
  rw [hsum.tsum_eq_zero_add]
  simp [radCoeff_zero]

/-- Termwise bound for the derivative series of `radSeries`, uniform on `Metric.ball 0 T`. -/
theorem norm_radCoeff_mul_deriv_le (hn : 1 ≤ n) (T : ℝ) (k : ℕ) {y : ℝ}
    (hy : y ∈ Metric.ball (0 : ℝ) T) :
    ‖radCoeff n ν k * ((k : ℝ) * y ^ (k - 1))‖ ≤
      (k : ℝ) * (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * T ^ (k - 1) := by
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
  have hTnn : (0:ℝ) ≤ T := (abs_nonneg y).trans hy.le
  have hbnd : |radCoeff n ν k| ≤ |ν| ^ k / (2 ^ k * (k.factorial : ℝ)) := abs_radCoeff_le hn k
  have hypow : |y| ^ (k - 1) ≤ T ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg y) hy.le (k - 1)
  have hnorm : ‖radCoeff n ν k * ((k : ℝ) * y ^ (k - 1))‖ =
      |radCoeff n ν k| * (k : ℝ) * |y| ^ (k - 1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)), abs_pow,
      ← mul_assoc]
  rw [hnorm]
  calc |radCoeff n ν k| * (k : ℝ) * |y| ^ (k - 1)
      ≤ (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * (k : ℝ) * T ^ (k - 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbnd (by positivity)) hypow (by positivity)
          (by positivity)
    _ = (k : ℝ) * (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * T ^ (k - 1) := by ring

/-- Summability of the uniform derivative bound on `Metric.ball 0 T`. -/
theorem summable_deriv_bound (_hn : 1 ≤ n) (T : ℝ) :
    Summable fun k : ℕ => (k : ℝ) * (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * T ^ (k - 1) := by
  have heq : ∀ j : ℕ,
      (|ν| / 2) * ((|ν| * T / 2) ^ j / (j.factorial : ℝ)) =
      ((j : ℝ) + 1) * (|ν| ^ (j + 1) / (2 ^ (j + 1) * ((j + 1).factorial : ℝ))) * T ^ (j + 1 - 1) := by
    intro j
    have hfact : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hνpow : |ν| ^ (j + 1) = |ν| ^ j * |ν| := by rw [pow_succ]
    have hidx1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hfactne : (j.factorial : ℝ) ≠ 0 := by positivity
    have h2ne : (2:ℝ) ^ j ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, hfact, hνpow, div_pow, mul_pow]
    field_simp
    ring
  have hshift : Summable (fun j : ℕ =>
      ((j : ℝ) + 1) * (|ν| ^ (j + 1) / (2 ^ (j + 1) * ((j + 1).factorial : ℝ))) * T ^ (j + 1 - 1)) :=
    (((Real.summable_pow_div_factorial (|ν| * T / 2)).mul_left (|ν| / 2))).congr heq
  have := (summable_nat_add_iff (f := fun k : ℕ =>
      (k : ℝ) * (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * T ^ (k - 1)) 1).mp
  apply this
  simpa using hshift

theorem hasDerivAt_radSeries (hn : 1 ≤ n) (s : ℝ) :
    HasDerivAt (radSeries n ν) (radSeries' n ν s) s := by
  set T := |s| + 1 with hTdef
  have hTpos : (0:ℝ) < T := by positivity
  have hmem : s ∈ Metric.ball (0:ℝ) T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hTdef]; linarith [abs_nonneg s]
  have hzero : (0:ℝ) ∈ Metric.ball (0:ℝ) T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_zero]; exact hTpos
  have hu : Summable fun k : ℕ => (k : ℝ) * (|ν| ^ k / (2 ^ k * (k.factorial : ℝ))) * T ^ (k - 1) :=
    summable_deriv_bound hn T
  have hg0 : Summable fun k => radCoeff n ν k * (0:ℝ) ^ k := summable_radSeries hn 0
  have key := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0:ℝ) T).isPreconnected
    (g := fun k (y : ℝ) => radCoeff n ν k * y ^ k)
    (g' := fun k (y : ℝ) => radCoeff n ν k * ((k : ℝ) * y ^ (k - 1)))
    (fun k y _ => (hasDerivAt_pow k y).const_mul (radCoeff n ν k))
    (fun k y hy => norm_radCoeff_mul_deriv_le hn T k hy)
    hzero hg0 hmem
  have hsummableD : Summable fun k => radCoeff n ν k * ((k : ℝ) * s ^ (k - 1)) :=
    Summable.of_norm_bounded hu (fun k => norm_radCoeff_mul_deriv_le hn T k hmem)
  have heq : (∑' k, radCoeff n ν k * ((k : ℝ) * s ^ (k - 1))) = radSeries' n ν s := by
    rw [hsummableD.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    unfold radSeries'
    refine tsum_congr (fun k => ?_)
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [heq] at key
  exact key

/-- Termwise bound for the derivative series of `radSeries'`, uniform on `Metric.ball 0 T`. -/
theorem norm_radCoeff_mul_deriv2_le (hn : 1 ≤ n) (T : ℝ) (k : ℕ) {y : ℝ}
    (hy : y ∈ Metric.ball (0 : ℝ) T) :
    ‖((k : ℝ) + 1) * radCoeff n ν (k + 1) * ((k : ℝ) * y ^ (k - 1))‖ ≤
      ((k : ℝ) + 1) * (k : ℝ) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) *
        T ^ (k - 1) := by
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
  have hTnn : (0:ℝ) ≤ T := (abs_nonneg y).trans hy.le
  have hbnd : |radCoeff n ν (k + 1)| ≤
      |ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) := abs_radCoeff_le hn (k + 1)
  have hypow : |y| ^ (k - 1) ≤ T ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg y) hy.le (k - 1)
  have hnorm : ‖((k : ℝ) + 1) * radCoeff n ν (k + 1) * ((k : ℝ) * y ^ (k - 1))‖ =
      ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| * (k : ℝ) * |y| ^ (k - 1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)), abs_pow]
    ring
  rw [hnorm]
  calc ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| * (k : ℝ) * |y| ^ (k - 1)
      ≤ ((k : ℝ) + 1) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * (k : ℝ) *
          T ^ (k - 1) := by
        have h1 : ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| ≤
            ((k : ℝ) + 1) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
        have h2 : ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| * (k : ℝ) * |y| ^ (k - 1) ≤
            ((k : ℝ) + 1) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * (k : ℝ) *
              |y| ^ (k - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
        exact h2.trans (mul_le_mul_of_nonneg_left hypow (by positivity))
    _ = ((k : ℝ) + 1) * (k : ℝ) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) *
          T ^ (k - 1) := by ring

theorem summable_deriv2_bound (T : ℝ) :
    Summable fun k : ℕ =>
      ((k : ℝ) + 1) * (k : ℝ) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) *
        T ^ (k - 1) := by
  have heq : ∀ j : ℕ,
      (|ν| / 2) ^ 2 * ((|ν| * T / 2) ^ j / (j.factorial : ℝ)) =
      (((j : ℝ) + 1) + 1) * ((j : ℝ) + 1) *
        (|ν| ^ (j + 1 + 1) / (2 ^ (j + 1 + 1) * ((j + 1 + 1).factorial : ℝ))) *
        T ^ (j + 1 - 1) := by
    intro j
    have hfact : ((j + 1 + 1).factorial : ℝ) =
        (((j : ℝ) + 1) + 1) * ((j : ℝ) + 1) * (j.factorial : ℝ) := by
      rw [show j + 1 + 1 = j + 2 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hνpow : |ν| ^ (j + 1 + 1) = |ν| ^ j * |ν| ^ 2 := by
      rw [show j + 1 + 1 = j + 2 from rfl, pow_add]
    have h2pow : (2:ℝ) ^ (j + 1 + 1) = 2 ^ j * 2 ^ 2 := by
      rw [show j + 1 + 1 = j + 2 from rfl, pow_add]
    have hidx1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hidx2 : (((j : ℝ) + 1) + 1) ≠ 0 := by positivity
    have hfactne : (j.factorial : ℝ) ≠ 0 := by positivity
    have h2ne : (2:ℝ) ^ j ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, hfact, hνpow, h2pow, div_pow, div_pow, mul_pow]
    field_simp
  have hshift : Summable (fun j : ℕ =>
      (((j : ℝ) + 1) + 1) * ((j : ℝ) + 1) *
        (|ν| ^ (j + 1 + 1) / (2 ^ (j + 1 + 1) * ((j + 1 + 1).factorial : ℝ))) * T ^ (j + 1 - 1)) :=
    (((Real.summable_pow_div_factorial (|ν| * T / 2)).mul_left ((|ν| / 2) ^ 2))).congr heq
  have hmp := (summable_nat_add_iff (f := fun k : ℕ =>
      ((k : ℝ) + 1) * (k : ℝ) *
        (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * T ^ (k - 1)) 1).mp
  apply hmp
  simpa using hshift

theorem hasDerivAt_radSeries' (hn : 1 ≤ n) (s : ℝ) :
    HasDerivAt (radSeries' n ν) (radSeries'' n ν s) s := by
  set T := |s| + 1 with hTdef
  have hTpos : (0:ℝ) < T := by positivity
  have hmem : s ∈ Metric.ball (0:ℝ) T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hTdef]; linarith [abs_nonneg s]
  have hzero : (0:ℝ) ∈ Metric.ball (0:ℝ) T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_zero]; exact hTpos
  have hu : Summable fun k : ℕ => ((k : ℝ) + 1) * (k : ℝ) *
      (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * T ^ (k - 1) :=
    summable_deriv2_bound T
  have hg0 : Summable fun (k : ℕ) => ((k : ℝ) + 1) * radCoeff n ν (k + 1) * (0:ℝ) ^ k :=
    summable_radSeries' hn 0
  have key := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0:ℝ) T).isPreconnected
    (g := fun (k : ℕ) (y : ℝ) => ((k : ℝ) + 1) * radCoeff n ν (k + 1) * y ^ k)
    (g' := fun (k : ℕ) (y : ℝ) => ((k : ℝ) + 1) * radCoeff n ν (k + 1) * ((k : ℝ) * y ^ (k - 1)))
    (fun (k : ℕ) y _ => (hasDerivAt_pow k y).const_mul (((k : ℝ) + 1) * radCoeff n ν (k + 1)))
    (fun (k : ℕ) y hy => norm_radCoeff_mul_deriv2_le hn T k hy)
    hzero hg0 hmem
  have hsummableD : Summable fun (k : ℕ) =>
      ((k : ℝ) + 1) * radCoeff n ν (k + 1) * ((k : ℝ) * s ^ (k - 1)) :=
    Summable.of_norm_bounded hu (fun k => norm_radCoeff_mul_deriv2_le hn T k hmem)
  have heq : (∑' k : ℕ, ((k : ℝ) + 1) * radCoeff n ν (k + 1) * ((k : ℝ) * s ^ (k - 1))) =
      radSeries'' n ν s := by
    rw [hsummableD.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    unfold radSeries''
    refine tsum_congr (fun k => ?_)
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [heq] at key
  exact key

/-- Termwise bound for the terms of `radSeries''`, uniform on `|y| ≤ T`. -/
theorem norm_radCoeff2_mul_pow_le (hn : 1 ≤ n) {y T : ℝ} (hy : |y| ≤ T) (k : ℕ) :
    ‖((k : ℝ) + 2) * ((k : ℝ) + 1) * radCoeff n ν (k + 2) * y ^ k‖ ≤
      (|ν| / 2) ^ 2 * ((|ν| * T / 2) ^ k / (k.factorial : ℝ)) := by
  have hTnn : (0:ℝ) ≤ T := (abs_nonneg y).trans hy
  have hbnd : |radCoeff n ν (k + 2)| ≤
      |ν| ^ (k + 2) / (2 ^ (k + 2) * ((k + 2).factorial : ℝ)) := abs_radCoeff_le hn (k + 2)
  have hypow : |y| ^ k ≤ T ^ k := pow_le_pow_left₀ (abs_nonneg y) hy k
  have hnorm : ‖((k : ℝ) + 2) * ((k : ℝ) + 1) * radCoeff n ν (k + 2) * y ^ k‖ =
      ((k : ℝ) + 2) * ((k : ℝ) + 1) * |radCoeff n ν (k + 2)| * |y| ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1), abs_pow]
  rw [hnorm]
  have h1 : ((k : ℝ) + 2) * ((k : ℝ) + 1) * |radCoeff n ν (k + 2)| ≤
      ((k : ℝ) + 2) * ((k : ℝ) + 1) * (|ν| ^ (k + 2) / (2 ^ (k + 2) * ((k + 2).factorial : ℝ))) :=
    mul_le_mul_of_nonneg_left hbnd (by positivity)
  calc ((k : ℝ) + 2) * ((k : ℝ) + 1) * |radCoeff n ν (k + 2)| * |y| ^ k
      ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) *
          (|ν| ^ (k + 2) / (2 ^ (k + 2) * ((k + 2).factorial : ℝ))) * T ^ k := by
        calc ((k : ℝ) + 2) * ((k : ℝ) + 1) * |radCoeff n ν (k + 2)| * |y| ^ k
            ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) *
                (|ν| ^ (k + 2) / (2 ^ (k + 2) * ((k + 2).factorial : ℝ))) * |y| ^ k :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) *
                (|ν| ^ (k + 2) / (2 ^ (k + 2) * ((k + 2).factorial : ℝ))) * T ^ k :=
              mul_le_mul_of_nonneg_left hypow (by positivity)
    _ = (|ν| / 2) ^ 2 * ((|ν| * T / 2) ^ k / (k.factorial : ℝ)) := by
        have hfact : ((k + 2).factorial : ℝ) =
            ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k.factorial : ℝ) := by
          rw [show k + 2 = k + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
          push_cast; ring
        have hνpow : |ν| ^ (k + 2) = |ν| ^ k * |ν| ^ 2 := by rw [pow_add]
        have h2pow : (2:ℝ) ^ (k + 2) = 2 ^ k * 2 ^ 2 := by rw [pow_add]
        have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
        have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
        have hfactne : (k.factorial : ℝ) ≠ 0 := by positivity
        have h2ne : (2:ℝ) ^ k ≠ 0 := by positivity
        rw [hfact, hνpow, h2pow, div_pow, div_pow, mul_pow]
        field_simp

theorem continuous_radSeries'' (hn : 1 ≤ n) :
    Continuous (radSeries'' n ν) := by
  rw [continuous_iff_continuousAt]
  intro s
  set T := |s| + 1 with hTdef
  have hTpos : (0:ℝ) < T := by positivity
  have hmem : s ∈ Metric.ball (0:ℝ) T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hTdef]; linarith [abs_nonneg s]
  have hbound_sum : Summable (fun k : ℕ => (|ν| / 2) ^ 2 * ((|ν| * T / 2) ^ k / (k.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (|ν| * T / 2)).mul_left ((|ν| / 2) ^ 2)
  have hcont : ContinuousOn (radSeries'' n ν) (Metric.ball (0:ℝ) T) := by
    unfold radSeries''
    refine continuousOn_tsum (fun k => ?_) hbound_sum (fun k y hy => ?_)
    · exact (continuous_const.mul (continuous_pow k)).continuousOn
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
      exact norm_radCoeff2_mul_pow_le hn hy.le k
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds hmem)

theorem deriv_radSeries (hn : 1 ≤ n) :
    deriv (radSeries n ν) = radSeries' n ν := by
  funext s
  exact (hasDerivAt_radSeries hn s).deriv

theorem deriv_radSeries' (hn : 1 ≤ n) :
    deriv (radSeries' n ν) = radSeries'' n ν := by
  funext s
  exact (hasDerivAt_radSeries' hn s).deriv

theorem contDiff_radSeries (hn : 1 ≤ n) :
    ContDiff ℝ 2 (radSeries n ν) := by
  have hdiff1 : Differentiable ℝ (radSeries' n ν) :=
    fun s => (hasDerivAt_radSeries' hn s).differentiableAt
  have hcont1 : Continuous (deriv (radSeries' n ν)) := by
    rw [deriv_radSeries' hn]; exact continuous_radSeries'' hn
  have hC1' : ContDiff ℝ 1 (radSeries' n ν) := contDiff_one_iff_deriv.2 ⟨hdiff1, hcont1⟩
  have hdiff0 : Differentiable ℝ (radSeries n ν) :=
    fun s => (hasDerivAt_radSeries hn s).differentiableAt
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hdiff0, by simp, ?_⟩
  rw [deriv_radSeries hn]
  exact hC1'

/-- `∑ k x^k / k!` is summable, for any real `x`. -/
theorem summable_nat_mul_pow_div_factorial (x : ℝ) :
    Summable (fun k : ℕ => (k : ℝ) * (x ^ k / (k.factorial : ℝ))) := by
  have heq : ∀ j : ℕ, x * (x ^ j / (j.factorial : ℝ)) =
      ((j : ℝ) + 1) * (x ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
    intro j
    have hfact : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hfactne : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [hfact, pow_succ]
    field_simp
  have hshift : Summable (fun j : ℕ =>
      ((j : ℝ) + 1) * (x ^ (j + 1) / ((j + 1).factorial : ℝ))) :=
    ((Real.summable_pow_div_factorial x).mul_left x).congr heq
  have hmp := (summable_nat_add_iff
      (f := fun k : ℕ => (k : ℝ) * (x ^ k / (k.factorial : ℝ))) 1).mp
  apply hmp
  simpa using hshift

/-- Summability of the coefficient sequence for `s * radSeries''`, reindexed to match
`radSeries'`'s indexing. -/
theorem summable_ode_aux (hn : 1 ≤ n) (s : ℝ) :
    Summable fun k : ℕ => (k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k := by
  apply Summable.of_norm_bounded
      ((summable_nat_mul_pow_div_factorial (|ν| * |s| / 2)).mul_left (|ν| / 2))
  intro k
  have hbnd : |radCoeff n ν (k + 1)| ≤
      |ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) := abs_radCoeff_le hn (k + 1)
  have hnorm : ‖(k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k‖ =
      (k : ℝ) * ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| * |s| ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1), abs_pow, ← mul_assoc]
  rw [hnorm]
  have h1 : (k : ℝ) * ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| ≤
      (k : ℝ) * ((k : ℝ) + 1) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) :=
    mul_le_mul_of_nonneg_left hbnd (by positivity)
  calc (k : ℝ) * ((k : ℝ) + 1) * |radCoeff n ν (k + 1)| * |s| ^ k
      ≤ (k : ℝ) * ((k : ℝ) + 1) * (|ν| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) *
          |s| ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = |ν| / 2 * ((k : ℝ) * ((|ν| * |s| / 2) ^ k / (k.factorial : ℝ))) := by
        have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hνpow : |ν| ^ (k + 1) = |ν| ^ k * |ν| := by rw [pow_succ]
        have h2pow : (2:ℝ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
        have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
        have hfactne : (k.factorial : ℝ) ≠ 0 := by positivity
        have h2ne : (2:ℝ) ^ k ≠ 0 := by positivity
        rw [hfact, hνpow, h2pow, div_pow, mul_pow]
        field_simp

/-- The ODE `4 s g'' + 2 n g' + ν g = 0`. -/
theorem radSeries_ode (hn : 1 ≤ n) (s : ℝ) :
    4 * s * radSeries'' n ν s + 2 * (n : ℝ) * radSeries' n ν s + ν * radSeries n ν s = 0 := by
  have h2 : Summable (fun k : ℕ => (k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k) :=
    summable_ode_aux hn s
  have hs_mul : s * radSeries'' n ν s =
      ∑' k : ℕ, (k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k := by
    unfold radSeries''
    rw [h2.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    push_cast
    rw [pow_succ]
    ring
  have step1 : 4 * s * radSeries'' n ν s =
      ∑' k : ℕ, 4 * ((k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1))) * s ^ k := by
    rw [mul_assoc, hs_mul, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    ring
  have step2 : 2 * (n : ℝ) * radSeries' n ν s =
      ∑' k : ℕ, 2 * (n : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k := by
    unfold radSeries'
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    ring
  have step3 : ν * radSeries n ν s = ∑' k : ℕ, ν * radCoeff n ν k * s ^ k := by
    unfold radSeries
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    ring
  have hsum1 : Summable
      (fun k : ℕ => 4 * ((k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1))) * s ^ k) := by
    have hh := h2.mul_left 4
    simpa [mul_assoc] using hh
  have hsum2 : Summable
      (fun k : ℕ => 2 * (n : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k) := by
    have hh := (summable_radSeries' (ν := ν) hn s).mul_left (2 * (n : ℝ))
    simpa [mul_assoc] using hh
  have hsum3 : Summable (fun k : ℕ => ν * radCoeff n ν k * s ^ k) := by
    have hh := (summable_radSeries (ν := ν) hn s).mul_left ν
    simpa [mul_assoc] using hh
  rw [step1, step2, step3, ← Summable.tsum_add hsum1 hsum2,
    ← Summable.tsum_add (hsum1.add hsum2) hsum3]
  have hterm : ∀ k : ℕ,
      4 * ((k : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1))) * s ^ k +
        2 * (n : ℝ) * (((k : ℝ) + 1) * radCoeff n ν (k + 1)) * s ^ k +
        ν * radCoeff n ν k * s ^ k = 0 := by
    intro k
    have hrec := radCoeff_rec (ν := ν) hn k
    linear_combination s ^ k * hrec
  simp only [hterm, tsum_zero]

end

end RobinCaps.Compact
