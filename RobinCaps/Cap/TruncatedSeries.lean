import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Sharp

/-!
# The truncated semicircular cap: Taylor expansion of `β_γ/α`

This file gives a rigorous version of the manuscript's expansion
(`reference/robin_endcaps_corrected_en.tex`, `eq:gamma-series`):

```
β_γ/α = π/4 + γ³/6 + γ⁵/40 + O(γ⁷).
```

By `RobinCaps.Cap.truncatedSemi_beta_div`, for `0 ≤ γ < 1` and `α ≠ 0`,
`(truncatedSemi γ hγ hγ1).beta α / α = g γ` where

```
g γ := (arccos γ + 2γ - γ√(1-γ²)) / 2.
```

We prove:
* `g_zero : g 0 = π/4`;
* `g_hasDerivAt : g'(γ) = 1 - √(1-γ²)` for `γ ∈ (-1,1)`;
* two-sided Taylor bounds for `√(1-t²)` on `t ∈ [0, 1/2]`, obtained by squaring
  (`sqrt_upper_taylor`, `sqrt_lower_taylor`);
* by integrating (via `monotoneOn_of_hasDerivWithinAt_nonneg`) these derivative
  bounds, the explicit two-sided bound
  `g_lower_bound`/`g_upper_bound`, combined into
  `g_expansion_bound : |g γ - (π/4 + γ³/6 + γ⁵/40)| ≤ γ⁷/56` for `0 ≤ γ ≤ 1/2`;
* the corollary for the cap functional, `truncatedSemi_beta_div_expansion`.
-/

open Set
open scoped Topology

namespace RobinCaps

namespace Cap

noncomputable section

/-! ## The explicit function `g γ := β_γ/α` -/

/-- `g γ` is the explicit value of `β_γ/α` for the truncated semicircular cap
(`truncatedSemi_beta_div`): `g γ = (arccos γ + 2γ - γ√(1-γ²))/2`. -/
def g (γ : ℝ) : ℝ := (Real.arccos γ + 2 * γ - γ * Real.sqrt (1 - γ ^ 2)) / 2

/-- **Item 1**: `g 0 = π/4`. -/
theorem g_zero : g 0 = Real.pi / 4 := by
  simp [g, Real.arccos_zero]
  ring

/-- **Item 2**: for `γ ∈ (-1,1)`, `g'(γ) = 1 - √(1-γ²)`.

Derivation: `d/dγ[arccos γ] = -1/√(1-γ²)` and
`d/dγ[γ√(1-γ²)] = √(1-γ²) - γ²/√(1-γ²)`, so
`2 g'(γ) = -1/√(1-γ²) + 2 - √(1-γ²) + γ²/√(1-γ²)
         = (γ²-1)/√(1-γ²) + 2 - √(1-γ²) = -√(1-γ²) + 2 - √(1-γ²) = 2(1-√(1-γ²))`,
using `(γ²-1)/√(1-γ²) = -(1-γ²)/√(1-γ²) = -√(1-γ²)`. -/
theorem g_hasDerivAt (γ : ℝ) (hγ : γ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt g (1 - Real.sqrt (1 - γ ^ 2)) γ := by
  obtain ⟨hγ1, hγ2⟩ := hγ
  have hne1 : γ ≠ (-1 : ℝ) := hγ1.ne'
  have hne2 : γ ≠ (1 : ℝ) := hγ2.ne
  have hpos : 0 < 1 - γ ^ 2 := by nlinarith
  set s := Real.sqrt (1 - γ ^ 2) with hs_def
  have hsq : s ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt hpos.le
  have hsne : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  -- derivative of `arccos`
  have h_arccos : HasDerivAt Real.arccos (-(1 / s)) γ :=
    Real.hasDerivAt_arccos hne1 hne2
  -- derivative of `2 * γ`
  have h_lin : HasDerivAt (fun x : ℝ => 2 * x) 2 γ := by
    simpa using (hasDerivAt_id γ).const_mul (2 : ℝ)
  -- derivative of `1 - x^2`
  have h_u : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * γ)) γ := by
    simpa using (hasDerivAt_pow 2 γ).const_sub (1 : ℝ)
  -- derivative of `√(1 - x^2)`
  have h_sqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      ((-(2 * γ)) / (2 * s)) γ := h_u.sqrt hpos.ne'
  -- derivative of `x * √(1 - x^2)`, product rule
  have h_prod : HasDerivAt (fun x : ℝ => x * Real.sqrt (1 - x ^ 2))
      (1 * s + γ * ((-(2 * γ)) / (2 * s))) γ :=
    (hasDerivAt_id γ).mul h_sqrt
  have h_sum : HasDerivAt (fun x : ℝ => Real.arccos x + 2 * x - x * Real.sqrt (1 - x ^ 2))
      ((-(1 / s)) + 2 - (1 * s + γ * ((-(2 * γ)) / (2 * s)))) γ :=
    (h_arccos.add h_lin).sub h_prod
  have h_div : HasDerivAt g
      (((-(1 / s)) + 2 - (1 * s + γ * ((-(2 * γ)) / (2 * s)))) / 2) γ := by
    unfold g
    exact h_sum.div_const 2
  have heq : (((-(1 / s)) + 2 - (1 * s + γ * ((-(2 * γ)) / (2 * s)))) / 2) = 1 - s := by
    field_simp
    linear_combination hsq
  rwa [heq] at h_div

/-! ## Taylor bounds for `√(1-t²)` -/

/-- Upper Taylor bound: `√(1-t²) ≤ 1 - t²/2 - t⁴/8`, for all `t` with `t² ≤ 1`.
Proved by squaring: `(1-t²/2-t⁴/8)² - (1-t²) = t⁶/8 + t⁸/64 ≥ 0`. -/
theorem sqrt_upper_taylor (t : ℝ) (ht : t ^ 2 ≤ 1) :
    Real.sqrt (1 - t ^ 2) ≤ 1 - t ^ 2 / 2 - t ^ 4 / 8 := by
  have hy : 0 ≤ 1 - t ^ 2 / 2 - t ^ 4 / 8 := by
    nlinarith [sq_nonneg (t ^ 2), sq_nonneg t]
  apply (Real.sqrt_le_left hy).mpr
  nlinarith [sq_nonneg (t ^ 3), sq_nonneg (t ^ 4)]

/-- Auxiliary polynomial inequality (single real variable), used to derive the
lower Taylor bound after substituting `x = t²`. -/
private theorem aux_cubic_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    (1 - x / 2 - x ^ 2 / 8 - x ^ 3 / 8) ^ 2 ≤ 1 - x := by
  nlinarith [mul_nonneg hx0 hx0, mul_nonneg (mul_nonneg hx0 hx0) hx0,
    mul_nonneg hx0 (sub_nonneg.mpr hx1),
    mul_nonneg (mul_nonneg hx0 hx0) (sub_nonneg.mpr hx1),
    mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hx1),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hx1)) hx0]

/-- Lower Taylor bound: `1 - t²/2 - t⁴/8 - t⁶/8 ≤ √(1-t²)`, for `0 ≤ t ≤ 1/2`.
Proved by squaring, using `aux_cubic_lower` with `x = t²`. -/
theorem sqrt_lower_taylor (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    1 - t ^ 2 / 2 - t ^ 4 / 8 - t ^ 6 / 8 ≤ Real.sqrt (1 - t ^ 2) := by
  have hx0 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have hx1 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have h := aux_cubic_lower (t ^ 2) hx0 hx1
  have e1 : (t ^ 2) ^ 2 = t ^ 4 := by ring
  have e2 : (t ^ 2) ^ 3 = t ^ 6 := by ring
  rw [e1, e2] at h
  exact Real.le_sqrt_of_sq_le h

/-! ## Integrating the derivative bounds -/

/-- `Icc 0 (1/2) ⊆ Ioo (-1) 1`. -/
private theorem Icc_subset_Ioo (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    x ∈ Set.Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The "lower" auxiliary function `g γ - (γ³/6 + γ⁵/40)`, whose derivative is
`(1-γ²/2-γ⁴/8) - √(1-γ²) ≥ 0` on `(0,1/2)` by `sqrt_upper_taylor`. -/
private def lowAux (γ : ℝ) : ℝ := g γ - (Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40)

private theorem lowAux_hasDerivAt (γ : ℝ) (hγ : γ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt lowAux ((1 - Real.sqrt (1 - γ ^ 2)) - (γ ^ 2 / 2 + γ ^ 4 / 8)) γ := by
  have hpoly : HasDerivAt (fun x : ℝ => Real.pi / 4 + x ^ 3 / 6 + x ^ 5 / 40)
      (γ ^ 2 / 2 + γ ^ 4 / 8) γ := by
    have hc := hasDerivAt_const γ (Real.pi / 4)
    have h3 := (hasDerivAt_pow 3 γ).div_const 6
    have h5 := (hasDerivAt_pow 5 γ).div_const 40
    have hsum := (hc.add h3).add h5
    convert hsum using 1
    push_cast
    ring
  exact (g_hasDerivAt γ hγ).sub hpoly

private theorem lowAux_monotoneOn : MonotoneOn lowAux (Set.Icc (0 : ℝ) (1 / 2)) := by
  have hf : ContinuousOn lowAux (Set.Icc (0 : ℝ) (1 / 2)) := fun x hx =>
    (lowAux_hasDerivAt x (Icc_subset_Ioo x hx)).continuousAt.continuousWithinAt
  have hf' : ∀ x ∈ interior (Set.Icc (0 : ℝ) (1 / 2)),
      HasDerivWithinAt lowAux ((1 - Real.sqrt (1 - x ^ 2)) - (x ^ 2 / 2 + x ^ 4 / 8))
        (interior (Set.Icc (0 : ℝ) (1 / 2))) x := by
    intro x hx
    rw [interior_Icc] at hx
    exact (lowAux_hasDerivAt x (Icc_subset_Ioo x (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
  have hf'0 : ∀ x ∈ interior (Set.Icc (0 : ℝ) (1 / 2)),
      0 ≤ (1 - Real.sqrt (1 - x ^ 2)) - (x ^ 2 / 2 + x ^ 4 / 8) := by
    intro x hx
    rw [interior_Icc] at hx
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    have := sqrt_upper_taylor x hx2
    linarith
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2)) hf hf' hf'0

/-- **Item 3, lower half**: for `0 ≤ γ ≤ 1/2`,
`π/4 + γ³/6 + γ⁵/40 ≤ g γ`. -/
theorem g_lower_bound (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) :
    Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40 ≤ g γ := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨le_refl 0, by norm_num⟩
  have hmemγ : γ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hγ0, hγ1⟩
  have hmono : lowAux 0 ≤ lowAux γ := lowAux_monotoneOn hmem0 hmemγ hγ0
  have h0 : lowAux 0 = 0 := by simp [lowAux, g_zero]
  have hγeq : lowAux γ = g γ - (Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40) := rfl
  linarith [hmono, h0, hγeq]

/-- The "upper" auxiliary function `(γ³/6 + γ⁵/40 + γ⁷/56) - g γ`, whose
derivative is `√(1-γ²) - (1-γ²/2-γ⁴/8-γ⁶/8) ≥ 0` on `(0,1/2)` by
`sqrt_lower_taylor`. -/
private def highAux (γ : ℝ) : ℝ := (Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40 + γ ^ 7 / 56) - g γ

private theorem highAux_hasDerivAt (γ : ℝ) (hγ : γ ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt highAux ((γ ^ 2 / 2 + γ ^ 4 / 8 + γ ^ 6 / 8) - (1 - Real.sqrt (1 - γ ^ 2))) γ := by
  have hpoly : HasDerivAt (fun x : ℝ => Real.pi / 4 + x ^ 3 / 6 + x ^ 5 / 40 + x ^ 7 / 56)
      (γ ^ 2 / 2 + γ ^ 4 / 8 + γ ^ 6 / 8) γ := by
    have hc := hasDerivAt_const γ (Real.pi / 4)
    have h3 := (hasDerivAt_pow 3 γ).div_const 6
    have h5 := (hasDerivAt_pow 5 γ).div_const 40
    have h7 := (hasDerivAt_pow 7 γ).div_const 56
    have hsum := ((hc.add h3).add h5).add h7
    convert hsum using 1
    push_cast
    ring
  exact hpoly.sub (g_hasDerivAt γ hγ)

private theorem highAux_monotoneOn : MonotoneOn highAux (Set.Icc (0 : ℝ) (1 / 2)) := by
  have hf : ContinuousOn highAux (Set.Icc (0 : ℝ) (1 / 2)) := fun x hx =>
    (highAux_hasDerivAt x (Icc_subset_Ioo x hx)).continuousAt.continuousWithinAt
  have hf' : ∀ x ∈ interior (Set.Icc (0 : ℝ) (1 / 2)),
      HasDerivWithinAt highAux
        ((x ^ 2 / 2 + x ^ 4 / 8 + x ^ 6 / 8) - (1 - Real.sqrt (1 - x ^ 2)))
        (interior (Set.Icc (0 : ℝ) (1 / 2))) x := by
    intro x hx
    rw [interior_Icc] at hx
    exact (highAux_hasDerivAt x (Icc_subset_Ioo x (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
  have hf'0 : ∀ x ∈ interior (Set.Icc (0 : ℝ) (1 / 2)),
      0 ≤ (x ^ 2 / 2 + x ^ 4 / 8 + x ^ 6 / 8) - (1 - Real.sqrt (1 - x ^ 2)) := by
    intro x hx
    rw [interior_Icc] at hx
    have := sqrt_lower_taylor x (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2)) hf hf' hf'0

/-- **Item 3, upper half**: for `0 ≤ γ ≤ 1/2`,
`g γ ≤ π/4 + γ³/6 + γ⁵/40 + γ⁷/56`. -/
theorem g_upper_bound (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) :
    g γ ≤ Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40 + γ ^ 7 / 56 := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨le_refl 0, by norm_num⟩
  have hmemγ : γ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hγ0, hγ1⟩
  have hmono : highAux 0 ≤ highAux γ := highAux_monotoneOn hmem0 hmemγ hγ0
  have h0 : highAux 0 = 0 := by simp [highAux, g_zero]
  have heqγ : highAux γ = (Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40 + γ ^ 7 / 56) - g γ := rfl
  linarith [hmono, h0, heqγ]

/-- **Item 3**: rigorous replacement for the manuscript's
`β_γ/α = π/4 + γ³/6 + γ⁵/40 + O(γ⁷)`: for `0 ≤ γ ≤ 1/2`,
`|g γ - (π/4 + γ³/6 + γ⁵/40)| ≤ γ⁷/56`. -/
theorem g_expansion_bound (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) :
    |g γ - (Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40)| ≤ γ ^ 7 / 56 := by
  have hlow := g_lower_bound γ hγ0 hγ1
  have hup := g_upper_bound γ hγ0 hγ1
  have hγ7 : 0 ≤ γ ^ 7 / 56 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-! ## Corollary for the cap functional -/

/-- **Item 4**: rigorous expansion for `β_γ/α` of the truncated semicircular cap,
`0 ≤ γ ≤ 1/2`: `|β_γ/α - (π/4 + γ³/6 + γ⁵/40)| ≤ γ⁷/56`. -/
theorem truncatedSemi_beta_div_expansion (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2) (α : ℝ)
    (hα : α ≠ 0) :
    |(truncatedSemi γ hγ (by linarith)).beta α / α -
        (Real.pi / 4 + γ ^ 3 / 6 + γ ^ 5 / 40)| ≤ (1 / 56) * γ ^ 7 := by
  rw [truncatedSemi_beta_div γ hγ (by linarith) α hα]
  have := g_expansion_bound γ hγ hγ1
  have heq : γ ^ 7 / 56 = (1 / 56) * γ ^ 7 := by ring
  rwa [heq] at this

end

end Cap

end RobinCaps
