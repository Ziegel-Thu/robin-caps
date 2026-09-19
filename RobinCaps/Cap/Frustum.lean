import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Checks

/-!
# The frustum cap: a flat terminal end perturbed linearly

This file formalizes the manuscript's "frustum" example: starting from the flat
cap (`θ ≡ 1`), perturb the profile linearly,
`θ_δ(s) = 1 - δ·χ(s)` with `K = 1` and `χ(s) = s + 1`,
and show that for all sufficiently small amplitudes `δ > 0` the effective end
coefficient strictly decreases: `β(C_δ) < α` (equivalently `𝓕(C_δ) < ω_m`),
matching the linearized prediction `β(C_δ)/α = 1 - κδ + O(δ²)` with
`κ = m/2 > 0` (`Cap.kappa`).
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

/-! ## The frustum profile and cap -/

/-- The **frustum cap**: axial length `K = 1`, profile `θ_δ(s) = 1 - δ·(s+1)`
(defined on all of `ℝ`, as is the convention for `Cap.θ`).  For small
`0 < δ < 1` this is an admissible profile: on `(-1,0)` it stays strictly
between `1-δ` and `1`, it is affine hence concave, and it is strictly
decreasing since `δ > 0`. -/
noncomputable def frustum (m : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) : Cap m where
  K := 1
  hK := one_pos
  θ := fun s => 1 - δ * (s + 1)
  θ_pos := by
    intro s hs
    have h1 : s + 1 < 1 := by linarith [hs.2]
    have h2 : (0 : ℝ) < s + 1 := by linarith [hs.1]
    nlinarith [mul_lt_mul_of_pos_left h1 hδ0]
  θ_le_one := by
    intro s hs
    have h2 : (0 : ℝ) < s + 1 := by linarith [hs.1]
    nlinarith [mul_pos hδ0 h2]
  θ_concave := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x _ y _ a b _ _ hab
    have hb : b = 1 - a := by linarith
    subst hb
    simp only [smul_eq_mul]
    refine le_of_eq ?_
    ring
  θ_antitone := by
    intro a _ b _ hab
    simp only
    nlinarith [mul_le_mul_of_nonneg_left hab hδ0.le]
  θ_tendsto := by
    have hcont : Continuous (fun s : ℝ => 1 - δ * (s + 1)) := by fun_prop
    have h := hcont.tendsto (-1)
    norm_num at h
    exact h.mono_left nhdsWithin_le_nhds
  θ_entrance := by norm_num
  θ_terminal := by
    have hcont : Continuous (fun s : ℝ => 1 - δ * (s + 1)) := by fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The frustum's `F` equals the raw `revF` formula with `K = 1` and
`χ(s) = s + 1`, since `Cap.F` is defined as `revolutionF`, which unfolds to
`revF m C.K C.θ` (`revF_eq`), and both fields of `frustum` reduce
definitionally. -/
theorem frustum_F_eq_fr (m : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (frustum m δ hδ0 hδ1).F = revF m 1 (fun s => 1 - δ * (s + 1)) := by
  rw [F_eq_revolutionF, revF_eq]
  rfl

/-! ## The linearized coefficient `κ = m/2` -/

/-- **The linearized coefficient of the frustum is `κ = m/2`.**
Here `χ(s) = s+1`, so `χ(0) = 1` and `∫_{-1}^0 χ = 1/2`, giving
`κ = m·(1 - 1/2) = m/2`. -/
theorem kappa_frustum_fr (m : ℕ) : kappa m 1 (fun s => s + 1) = (m : ℝ) / 2 := by
  have hintId : IntervalIntegrable (fun s : ℝ => s) volume (-1) 0 :=
    continuous_id.intervalIntegrable _ _
  have hintConst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-1) 0 :=
    continuous_const.intervalIntegrable _ _
  have hsum : (∫ s in (-1 : ℝ)..0, (s + 1)) =
      (∫ s in (-1 : ℝ)..0, s) + ∫ _s in (-1 : ℝ)..0, (1 : ℝ) :=
    intervalIntegral.integral_add hintId hintConst
  rw [kappa]
  rw [hsum, integral_id, intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  ring

/-! ## Strict decrease of `F` (hence of `β`) for small amplitudes -/

/-- **The frustum's `F` is strictly below `ω_m` for all small amplitudes
`0 < δ < δ₀`.**  This is the paper's headline claim in explicit-functional
form: since `β(C_δ)/α = F(C_δ)/ω_m = 1 - κδ + O(δ²)` with `κ = m/2 > 0`
(`linearization_bound`, `kappa_frustum_fr`), for `δ` small enough the `O(δ²)`
remainder cannot overcome the strictly negative linear term. -/
theorem frustum_F_lt_omega_fr (m : ℕ) (hm : 1 ≤ m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1), δ < δ₀ →
        (frustum m δ hδ0 hδ1).F < omega m := by
  obtain ⟨C, hC0, hbound⟩ := linearization_bound m hm 1 one_pos
    (fun s => s + 1) (fun _ => 1) 1 1
    (fun s _ => (hasDerivAt_id s).add_const (1 : ℝ))
    continuousOn_const
    (fun s hs => by linarith [hs.1])
    (fun s hs => by linarith [hs.2])
    (fun s _ => by norm_num)
    (by norm_num) (by norm_num)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  refine ⟨min (1 / 2) ((m : ℝ) / (2 * (C + 1))), ?_, min_le_left _ _, ?_⟩
  · apply lt_min (by norm_num)
    positivity
  · intro δ hδ0 hδ1 hδlt
    have hδhalf : δ * (1 : ℝ) ≤ 1 / 2 := by
      have := hδlt.le.trans (min_le_left (1 / 2) ((m : ℝ) / (2 * (C + 1))))
      nlinarith
    have hb := hbound δ hδ0.le hδhalf
    rw [kappa_frustum_fr] at hb
    have hδlt' : δ < (m : ℝ) / (2 * (C + 1)) :=
      lt_of_lt_of_le hδlt (min_le_right _ _)
    have hclear : δ * (2 * (C + 1)) < (m : ℝ) :=
      (lt_div_iff₀ (by positivity)).mp hδlt'
    have hCδ : C * δ < (m : ℝ) / 2 := by nlinarith [hclear]
    have hCδ2 : C * δ ^ 2 < (m : ℝ) / 2 * δ := by
      have := mul_lt_mul_of_pos_right hCδ hδ0
      calc C * δ ^ 2 = C * δ * δ := by ring
        _ < (m : ℝ) / 2 * δ := this
    have hratio : revF m 1 (fun s => 1 - δ * (s + 1)) / omega m < 1 := by
      have h1 := (abs_le.mp hb).2
      nlinarith [hCδ2]
    rw [frustum_F_eq_fr]
    exact (div_lt_one (omega_pos m)).mp hratio

/-- **The frustum's effective end coefficient `β(C_δ)` is strictly below `α`
for all small amplitudes.**  Immediate from `frustum_F_lt_omega_fr` since
`β(C,α) = (α/ω_m)·F(C)` is strictly monotone in `F(C)` for `α > 0`. -/
theorem frustum_beta_lt_fr (m : ℕ) (hm : 1 ≤ m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1), δ < δ₀ →
        ∀ α : ℝ, 0 < α → (frustum m δ hδ0 hδ1).beta α < α := by
  obtain ⟨δ₀, hδ₀pos, hδ₀half, hδ₀prop⟩ := frustum_F_lt_omega_fr m hm
  refine ⟨δ₀, hδ₀pos, hδ₀half, ?_⟩
  intro δ hδ0 hδ1 hδlt α hα
  have hF := hδ₀prop δ hδ0 hδ1 hδlt
  have hpos : 0 < α / omega m := div_pos hα (omega_pos m)
  have hmul := mul_lt_mul_of_pos_left hF hpos
  rw [div_mul_cancel₀ α (omega_ne_zero m)] at hmul
  rw [beta]
  exact hmul
