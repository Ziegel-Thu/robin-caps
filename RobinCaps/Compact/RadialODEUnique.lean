import Mathlib

/-!
# Uniqueness for the singular radial ODE `4 s g'' + 2 n g' + ν g = 0`

This file proves the uniqueness statement needed later: a `C²` solution of
`4 s g'' + 2 n g' + ν g = 0` on `(0, ∞)` that vanishes together with its derivative at some
`s₀ > 0` vanishes identically on `(0, ∞)`, and hence (by continuity) also at `s = 0`.

The proof rewrites the second-order ODE as a first-order system for
`y s = (g s, deriv g s)` with vector field
`v s (p₁, p₂) = (p₂, -(2 n p₂ + ν p₁) / (4 s))`,
which is Lipschitz in `p` (uniformly for `s` in a compact interval bounded away from `0`), and
invokes Mathlib's Grönwall-based ODE uniqueness theorem
(`ODE_solution_unique_of_mem_Ioo` in `Mathlib.Analysis.ODE.Gronwall`) to compare `y` with the
zero solution.
-/

namespace RobinCaps.Compact

open Set Filter Topology

/-- **Uniqueness.** If `g` is `C²`, solves `4 s g'' + 2 n g' + ν g = 0` on `(0, ∞)`, and `g` and
`g'` both vanish at some `s₀ > 0`, then `g` vanishes on `(0, ∞)`; in particular `g 0 = 0` by
continuity. -/
theorem radialODE_zero_of_zero_deriv_zero {n : ℕ} {ν : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hode : ∀ s : ℝ, 0 < s → 4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s + ν * g s = 0)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (h0 : g s₀ = 0) (h1 : deriv g s₀ = 0) :
    ∀ s : ℝ, 0 < s → g s = 0 := by
  -- Derivative facts coming from `C²`-regularity.
  have hg1 : ∀ t : ℝ, HasDerivAt g (deriv g t) t := fun t =>
    (hg.differentiable (by norm_num)) t |>.hasDerivAt
  have hg2 : ∀ t : ℝ, HasDerivAt (deriv g) (deriv (deriv g) t) t := fun t =>
    (hg.differentiable_deriv_two) t |>.hasDerivAt
  intro s hs
  -- Choose a window `Ioo a b`, bounded away from `0`, containing both `s₀` and `s`.
  set a : ℝ := min s₀ s / 2 with ha_def
  set b : ℝ := max s₀ s + 1 with hb_def
  have hmin_pos : 0 < min s₀ s := lt_min hs₀ hs
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have hs₀_mem : s₀ ∈ Ioo a b := by
    refine ⟨?_, ?_⟩
    · have h1' : a ≤ s₀ / 2 := by rw [ha_def]; gcongr; exact min_le_left _ _
      linarith
    · have h2' : s₀ ≤ max s₀ s := le_max_left _ _
      rw [hb_def]; linarith
  have hs_mem : s ∈ Ioo a b := by
    refine ⟨?_, ?_⟩
    · have h1' : a ≤ s / 2 := by rw [ha_def]; gcongr; exact min_le_right _ _
      linarith
    · have h2' : s ≤ max s₀ s := le_max_right _ _
      rw [hb_def]; linarith
  -- Lipschitz constant for the vector field, uniform on `Ioo a b` (using `a > 0`).
  set K0 : ℝ := max 1 ((2 * (n : ℝ) + |ν|) / (4 * a)) with hK0_def
  have hK0_ge : (2 * (n : ℝ) + |ν|) / (4 * a) ≤ K0 := le_max_right _ _
  have hv : ∀ t ∈ Ioo a b, LipschitzOnWith (Real.toNNReal K0)
      (fun p : ℝ × ℝ => (p.2, -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t))) (univ : Set (ℝ × ℝ)) := by
    intro t ht
    have ht0 : 0 < t := ha_pos.trans ht.1
    have hat : a < t := ht.1
    apply LipschitzOnWith.of_dist_le'
    rintro p - q -
    show dist (p.2, -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t))
        (q.2, -(2 * (n : ℝ) * q.2 + ν * q.1) / (4 * t)) ≤ K0 * dist p q
    rw [Prod.dist_eq]
    apply max_le
    · calc dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ ≤ K0 * dist p q := by
          nlinarith [dist_nonneg (x := p) (y := q),
            le_max_left (1 : ℝ) ((2 * (n : ℝ) + |ν|) / (4 * a))]
    · have hpd1 : |p.1 - q.1| ≤ dist p q := by
        rw [Prod.dist_eq]; exact (le_max_left _ _).trans_eq' (Real.dist_eq p.1 q.1)
      have hpd2 : |p.2 - q.2| ≤ dist p q := by
        rw [Prod.dist_eq]; exact (le_max_right _ _).trans_eq' (Real.dist_eq p.2 q.2)
      have hdnn : 0 ≤ dist p q := dist_nonneg
      rw [Real.dist_eq]
      have habs_eq : -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t) -
          -(2 * (n : ℝ) * q.2 + ν * q.1) / (4 * t)
          = (2 * (n : ℝ) * (q.2 - p.2) + ν * (q.1 - p.1)) / (4 * t) := by
        field_simp; ring
      rw [habs_eq, abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * t)]
      have e1 : |2 * (n : ℝ) * (q.2 - p.2)| ≤ 2 * (n : ℝ) * dist p q := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (n : ℝ))]
        gcongr
        rw [abs_sub_comm]; exact hpd2
      have e2 : |ν * (q.1 - p.1)| ≤ |ν| * dist p q := by
        rw [abs_mul]
        gcongr
        rw [abs_sub_comm]; exact hpd1
      have htri : |2 * (n : ℝ) * (q.2 - p.2) + ν * (q.1 - p.1)| ≤
          2 * (n : ℝ) * dist p q + |ν| * dist p q :=
        (abs_add_le _ _).trans (add_le_add e1 e2)
      calc |2 * (n : ℝ) * (q.2 - p.2) + ν * (q.1 - p.1)| / (4 * t)
          ≤ (2 * (n : ℝ) * dist p q + |ν| * dist p q) / (4 * t) := by gcongr
        _ = ((2 * (n : ℝ) + |ν|) / (4 * t)) * dist p q := by ring
        _ ≤ ((2 * (n : ℝ) + |ν|) / (4 * a)) * dist p q := by gcongr
        _ ≤ K0 * dist p q := mul_le_mul_of_nonneg_right hK0_ge hdnn
  -- `y = (g, g')` solves the first-order system.
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun t => (g t, deriv g t))
      ((fun (t : ℝ) (p : ℝ × ℝ) => (p.2, -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t))) t
        (g t, deriv g t)) t := by
    intro t ht
    have ht0 : 0 < t := ha_pos.trans ht.1
    have hne : (4 * t : ℝ) ≠ 0 := by positivity
    have heq2 : deriv (deriv g) t = -(2 * (n : ℝ) * deriv g t + ν * g t) / (4 * t) := by
      rw [eq_div_iff hne]
      linear_combination hode t ht0
    have hd := (hg1 t).prodMk (hg2 t)
    simp only
    rw [heq2] at hd
    exact hd
  -- The zero function solves the same system.
  have hzero : ∀ t ∈ Ioo a b, HasDerivAt (fun _ : ℝ => ((0:ℝ), (0:ℝ)))
      ((fun (t : ℝ) (p : ℝ × ℝ) => (p.2, -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t))) t
        ((0:ℝ), (0:ℝ))) t := by
    intro t ht
    have hz : ((fun (t : ℝ) (p : ℝ × ℝ) => (p.2, -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t))) t
        ((0:ℝ), (0:ℝ))) = ((0:ℝ), (0:ℝ)) := by simp
    rw [hz]
    exact hasDerivAt_const t (0, 0)
  have heq : (fun t => (g t, deriv g t)) s₀ = (fun _ : ℝ => ((0:ℝ), (0:ℝ))) s₀ := by
    simp [h0, h1]
  -- Apply Mathlib's Grönwall-based ODE uniqueness and evaluate at `s`.
  have hmain := ODE_solution_unique_of_mem_Ioo
    (v := fun (t : ℝ) (p : ℝ × ℝ) => (p.2, -(2 * (n : ℝ) * p.2 + ν * p.1) / (4 * t)))
    (s := fun _ : ℝ => (univ : Set (ℝ × ℝ)))
    hv hs₀_mem (fun t ht => ⟨hderiv t ht, mem_univ _⟩) (fun t ht => ⟨hzero t ht, mem_univ _⟩) heq
  have hval := hmain hs_mem
  simpa using congrArg Prod.fst hval

/-- In particular `g` also vanishes at `s = 0`, by continuity. -/
theorem radialODE_zero_at_zero {n : ℕ} {ν : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hode : ∀ s : ℝ, 0 < s → 4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s + ν * g s = 0)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (h0 : g s₀ = 0) (h1 : deriv g s₀ = 0) : g 0 = 0 := by
  have hz : ∀ s : ℝ, 0 < s → g s = 0 :=
    radialODE_zero_of_zero_deriv_zero hg hode hs₀ h0 h1
  have hcont : ContinuousAt g 0 := hg.continuous.continuousAt
  have htendsto : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds hcont
  have htendsto0 : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
    tendsto_nhds_of_eventually_eq
      (by filter_upwards [self_mem_nhdsWithin] with x hx using hz x hx)
  exact tendsto_nhds_unique htendsto htendsto0

end RobinCaps.Compact
