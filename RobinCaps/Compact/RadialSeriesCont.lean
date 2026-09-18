import RobinCaps.Compact.RadialSeries

/-!
# Continuity of the radial series in `(ν, s)`

This file establishes joint continuity of `radSeries`/`radSeries'` in the pair `(ν, s)`,
continuity in each variable separately, the degenerate case `ν = 0`, and the ODE rewritten
with `deriv`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.Compact

open Filter Topology

variable {n : ℕ}

noncomputable section

/-- The coefficients are polynomial in `ν`, hence continuous. -/
theorem continuous_radCoeff (n : ℕ) (k : ℕ) : Continuous fun ν : ℝ => radCoeff n ν k := by
  induction k with
  | zero =>
      have h : (fun ν : ℝ => radCoeff n ν 0) = fun _ => (1 : ℝ) := funext fun ν => radCoeff_zero
      rw [h]; exact continuous_const
  | succ k ih =>
      have h : (fun ν : ℝ => radCoeff n ν (k + 1)) =
          fun ν : ℝ => -ν * radCoeff n ν k / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + n)) :=
        funext fun ν => radCoeff_succ k
      rw [h]
      exact (continuous_neg.mul ih).div_const _

/-- Helper: on the open ball of radius `N` around `0` in `ℝ × ℝ`, both coordinates are
bounded by `N` in absolute value. -/
private theorem abs_le_of_mem_ball {N : ℝ} {p : ℝ × ℝ} (hp : p ∈ Metric.ball (0 : ℝ × ℝ) N) :
    |p.1| ≤ N ∧ |p.2| ≤ N := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, Prod.norm_def, max_lt_iff] at hp
  refine ⟨?_, ?_⟩
  · rw [← Real.norm_eq_abs]; exact hp.1.le
  · rw [← Real.norm_eq_abs]; exact hp.2.le

/-- Joint continuity of the series in `(ν, s)`. -/
theorem continuous_radSeries_pair (hn : 1 ≤ n) :
    Continuous fun p : ℝ × ℝ => radSeries n p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set N : ℝ := ‖p₀‖ + 1 with hN_def
  have hN0 : 0 < N := by positivity
  have hp₀ : p₀ ∈ Metric.ball (0 : ℝ × ℝ) N := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_add_one _
  have hmem : Metric.ball (0 : ℝ × ℝ) N ∈ 𝓝 p₀ := Metric.isOpen_ball.mem_nhds hp₀
  have hcont : ContinuousOn (fun p : ℝ × ℝ => radSeries n p.1 p.2)
      (Metric.ball (0 : ℝ × ℝ) N) := by
    unfold radSeries
    refine continuousOn_tsum (u := fun k => (N * N / 2) ^ k / k.factorial)
      (fun k => (((continuous_radCoeff n k).comp continuous_fst).mul
        (continuous_snd.pow k)).continuousOn)
      (Real.summable_pow_div_factorial (N * N / 2)) ?_
    intro k p hp
    obtain ⟨h1, h2⟩ := abs_le_of_mem_ball hp
    have hb := abs_radCoeff_mul_pow_le (n := n) (ν := p.1) hn h2 k
    calc ‖radCoeff n p.1 k * p.2 ^ k‖ = |radCoeff n p.1 k * p.2 ^ k| := Real.norm_eq_abs _
      _ ≤ (|p.1| * N / 2) ^ k / k.factorial := hb
      _ ≤ (N * N / 2) ^ k / k.factorial := by gcongr
  exact hcont.continuousAt hmem

theorem continuous_radSeries'_pair (hn : 1 ≤ n) :
    Continuous fun p : ℝ × ℝ => radSeries' n p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set N : ℝ := ‖p₀‖ + 1 with hN_def
  have hN0 : 0 < N := by positivity
  have hp₀ : p₀ ∈ Metric.ball (0 : ℝ × ℝ) N := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_add_one _
  have hmem : Metric.ball (0 : ℝ × ℝ) N ∈ 𝓝 p₀ := Metric.isOpen_ball.mem_nhds hp₀
  have hcont : ContinuousOn (fun p : ℝ × ℝ => radSeries' n p.1 p.2)
      (Metric.ball (0 : ℝ × ℝ) N) := by
    unfold radSeries'
    refine continuousOn_tsum
      (fun k => ((((continuous_const.mul
        ((continuous_radCoeff n (k + 1)).comp continuous_fst))).mul
        (continuous_snd.pow k))).continuousOn)
      ((Real.summable_pow_div_factorial (N * N / 2)).mul_left (N / 2)) ?_
    intro k p hp
    obtain ⟨h1, h2⟩ := abs_le_of_mem_ball hp
    have hbnd : |radCoeff n p.1 (k + 1)| ≤
        |p.1| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) := abs_radCoeff_le hn (k + 1)
    have hnorm : ‖((k : ℝ) + 1) * radCoeff n p.1 (k + 1) * p.2 ^ k‖ =
        ((k : ℝ) + 1) * |radCoeff n p.1 (k + 1)| * |p.2| ^ k := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1),
        abs_pow]
    rw [hnorm]
    have step1 : ((k : ℝ) + 1) * |radCoeff n p.1 (k + 1)| * |p.2| ^ k ≤
        ((k : ℝ) + 1) * (|p.1| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * N ^ k := by
      have hpk : |p.2| ^ k ≤ N ^ k := pow_le_pow_left₀ (abs_nonneg p.2) h2 k
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbnd (by positivity)) hpk (by positivity)
        (by positivity)
    have step2 : ((k : ℝ) + 1) * (|p.1| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) *
        N ^ k ≤ (N / 2) * ((N * N / 2) ^ k / k.factorial) := by
      have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hidx1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hfactne : (k.factorial : ℝ) ≠ 0 := by positivity
      have heq : ((k : ℝ) + 1) * (|p.1| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) *
          N ^ k = (|p.1| / 2) * ((|p.1| * N / 2) ^ k / k.factorial) := by
        rw [hfact, pow_succ, div_pow, mul_pow]
        field_simp
        ring
      rw [heq]
      have hb1 : |p.1| / 2 ≤ N / 2 := by linarith
      have hb2 : (|p.1| * N / 2) ^ k ≤ (N * N / 2) ^ k := by
        gcongr
      have hb1' : 0 ≤ |p.1| / 2 := by positivity
      calc (|p.1| / 2) * ((|p.1| * N / 2) ^ k / k.factorial)
          ≤ (N / 2) * ((|p.1| * N / 2) ^ k / k.factorial) := by
            gcongr
        _ ≤ (N / 2) * ((N * N / 2) ^ k / k.factorial) := by
            gcongr
    calc ((k : ℝ) + 1) * |radCoeff n p.1 (k + 1)| * |p.2| ^ k
        ≤ ((k : ℝ) + 1) * (|p.1| ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * N ^ k :=
          step1
      _ ≤ (N / 2) * ((N * N / 2) ^ k / k.factorial) := step2
  exact hcont.continuousAt hmem

/-- Continuity in `ν` for fixed `s`, and in `s` for fixed `ν`. -/
theorem continuous_radSeries_nu (hn : 1 ≤ n) (s : ℝ) :
    Continuous fun ν : ℝ => radSeries n ν s :=
  (continuous_radSeries_pair hn).comp (continuous_id.prodMk continuous_const)

theorem continuous_radSeries'_nu (hn : 1 ≤ n) (s : ℝ) :
    Continuous fun ν : ℝ => radSeries' n ν s :=
  (continuous_radSeries'_pair hn).comp (continuous_id.prodMk continuous_const)

theorem continuous_radSeries (hn : 1 ≤ n) (ν : ℝ) :
    Continuous (radSeries n ν) :=
  (continuous_radSeries_pair hn).comp (continuous_const.prodMk continuous_id)

/-- At `ν = 0` the series is the constant `1`. -/
theorem radCoeff_zero_nu (n : ℕ) (k : ℕ) (hk : 1 ≤ k) : radCoeff n 0 k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  simp [radCoeff_succ]

theorem radSeries_zero_nu (hn : 1 ≤ n) (s : ℝ) : radSeries n 0 s = 1 := by
  unfold radSeries
  have hsum : Summable fun k => radCoeff n (0:ℝ) k * s ^ k := summable_radSeries hn s
  have hf : ∀ k, 1 ≤ k → radCoeff n (0:ℝ) k * s ^ k = 0 := by
    intro k hk
    rw [radCoeff_zero_nu n k hk, zero_mul]
  have := hasSum_single (f := fun k => radCoeff n (0:ℝ) k * s ^ k) 0
    (fun k hk => hf k (Nat.one_le_iff_ne_zero.mpr hk))
  rw [this.tsum_eq]
  simp [radCoeff_zero]

theorem radSeries'_zero_nu (hn : 1 ≤ n) (s : ℝ) : radSeries' n 0 s = 0 := by
  have _hn := hn
  unfold radSeries'
  have : (fun k : ℕ => ((k : ℝ) + 1) * radCoeff n (0:ℝ) (k + 1) * s ^ k) = fun _ => (0:ℝ) := by
    funext k
    rw [radCoeff_zero_nu n (k + 1) (by omega), mul_zero, zero_mul]
  rw [this, tsum_zero]

/-- The ODE in the form with `deriv`, valid for all `s`. -/
theorem radSeries_ode' (hn : 1 ≤ n) (ν s : ℝ) :
    4 * s * deriv (deriv (radSeries n ν)) s + 2 * (n : ℝ) * deriv (radSeries n ν) s +
      ν * radSeries n ν s = 0 := by
  rw [deriv_radSeries hn, deriv_radSeries' hn]
  exact radSeries_ode hn s

end

end RobinCaps.Compact
