import Mathlib
import RobinCaps.Domain.Thin
import RobinCaps.Domain.CapsuleThin

/-!
# The diameter of the thin domain for arbitrary admissible caps

For two *hemispherical* caps the Euclidean diameter of the thin domain is
exactly `L` (`euclidDiam_thinDomain_hemisphere` in `Domain/CapsuleThin.lean`).
For **arbitrary** admissible caps `C₋`, `C₊` the manuscript only claims the
two-sided bound `eq:diam-bound`

`L ≤ diam Ω_R ≤ √(L² + 4R²) ≤ L + 2R²/L`,

i.e. `diam Ω_R = L + O(R²)`.  This file proves exactly that.

## Main results

* `euclidDiam_thinDomain_le`: `diam Ω_R ≤ √(L² + 4R²)`;
* `le_euclidDiam_thinDomain`: `L ≤ diam Ω_R`;
* `euclidDiam_thinDomain_le_add`: `diam Ω_R ≤ L + 2R²/L`;
* `euclidDiam_thinDomain_bounds`: the two-sided statement `eq:diam-bound`.

The "diameter" here is `euclidDiam`, the *Euclidean* diameter of the image of
`Ω_R ⊆ CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)` under the identification
`toEuclid m : CapSpace m → EuclideanSpace ℝ (Fin (m+1))`; the ambient metric on
the product `CapSpace m` is the sup metric, which is *not* the manuscript's.
For completeness the corresponding sup-metric statements are also recorded
(`diam_thinDomain_le`, `le_diam_thinDomain`).

The proof is elementary: two points of `Ω_R` have axial separation `< L` (both
axial coordinates lie in `(-L/2, L/2)`) and transverse separation `< 2R` (both
transverse parts have norm `< r_R ≤ R`), whence `dist² < L² + 4R²`; conversely
the axial points `(x, 0)`, `x ∈ (-L/2, L/2)`, all lie in `Ω_R` because
`r_R > 0`, and they realise separations arbitrarily close to `L`.
-/

open MeasureTheory Set Metric
open scoped Topology ENNReal

namespace RobinCaps
namespace Domain

open RobinCaps.Cap

noncomputable section

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## The pairwise distance bound -/

/-- Any two points of `Ω_R` are at Euclidean distance at most `√(L² + 4R²)`:
the axial separation is `< L` and the transverse separation is `< 2R`. -/
theorem dist_toEuclid_le_of_mem_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {p q : CapSpace m} (hp : p ∈ thinDomain Cm Cp L R) (hq : q ∈ thinDomain Cm Cp L R) :
    dist (toEuclid m p) (toEuclid m q) ≤ Real.sqrt (L ^ 2 + 4 * R ^ 2) := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hpz : ‖p.2‖ < R := lt_of_lt_of_le hp3 (profile_le_R hR hL ⟨hp1, hp2⟩)
  have hqz : ‖q.2‖ < R := lt_of_lt_of_le hq3 (profile_le_R hR hL ⟨hq1, hq2⟩)
  -- axial separation
  have hax : (p.1 - q.1) ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ L - (p.1 - q.1) by linarith)
      (show (0:ℝ) ≤ L + (p.1 - q.1) by linarith)]
  -- transverse separation
  have htr : ‖p.2 - q.2‖ ≤ ‖p.2‖ + ‖q.2‖ := norm_sub_le _ _
  have htr2 : ‖p.2 - q.2‖ ^ 2 ≤ 4 * R ^ 2 := by
    nlinarith [norm_nonneg (p.2 - q.2), norm_nonneg p.2, norm_nonneg q.2]
  have hsq : dist (toEuclid m p) (toEuclid m q) ^ 2 ≤ L ^ 2 + 4 * R ^ 2 := by
    rw [dist_toEuclid_sq]; linarith
  have h0 : 0 ≤ dist (toEuclid m p) (toEuclid m q) := dist_nonneg
  calc dist (toEuclid m p) (toEuclid m q)
      = Real.sqrt (dist (toEuclid m p) (toEuclid m q) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (L ^ 2 + 4 * R ^ 2) := Real.sqrt_le_sqrt hsq

/-- The Euclidean image of the thin domain is bounded. -/
theorem isBounded_toEuclid_image_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Bornology.IsBounded (toEuclid m '' thinDomain Cm Cp L R) := by
  rw [Metric.isBounded_iff]
  refine ⟨Real.sqrt (L ^ 2 + 4 * R ^ 2), ?_⟩
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  exact dist_toEuclid_le_of_mem_thinDomain hR hL hp hq

/-! ## The upper bound `diam Ω_R ≤ √(L² + 4R²)` -/

/-- **Upper bound for the diameter of the thin domain** (manuscript
`eq:diam-bound`): `diam Ω_R ≤ √(L² + 4R²)` for arbitrary admissible caps. -/
theorem euclidDiam_thinDomain_le (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    euclidDiam (thinDomain Cm Cp L R) ≤ Real.sqrt (L ^ 2 + 4 * R ^ 2) := by
  simp only [euclidDiam]
  refine Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg _) ?_
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  exact dist_toEuclid_le_of_mem_thinDomain hR hL hp hq

/-! ## The lower bound `L ≤ diam Ω_R` -/

/-- The axial points `(x, 0)`, `x ∈ (-L/2, L/2)`, belong to `Ω_R` (the profile
is strictly positive on the whole axial interval). -/
theorem axialPoint_mem_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : x ∈ Ioo (-L/2) (L/2)) : ((x, 0) : CapSpace m) ∈ thinDomain Cm Cp L R :=
  ⟨hx.1, hx.2, by simpa using profile_pos hR hL hx⟩

/-- For every `0 < ε ≤ L/2` the two axial points `(∓L/2 ± ε, 0)` witness
`L - 2ε ≤ diam Ω_R`. -/
theorem sub_le_euclidDiam_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {ε : ℝ} (hε : 0 < ε) (hεL : ε ≤ L/2) :
    L - 2 * ε ≤ euclidDiam (thinDomain Cm Cp L R) := by
  have hL0 : 0 < L := span_pos (Cm := Cm) (Cp := Cp) hR hL
  have hmem1 : ((-L/2 + ε, 0) : CapSpace m) ∈ thinDomain Cm Cp L R :=
    axialPoint_mem_thinDomain hR hL ⟨by linarith, by linarith⟩
  have hmem2 : ((L/2 - ε, 0) : CapSpace m) ∈ thinDomain Cm Cp L R :=
    axialPoint_mem_thinDomain hR hL ⟨by linarith, by linarith⟩
  have hd := Metric.dist_le_diam_of_mem (isBounded_toEuclid_image_thinDomain hR hL)
    (mem_image_of_mem (toEuclid m) hmem1) (mem_image_of_mem (toEuclid m) hmem2)
  have hsq := dist_toEuclid_sq ((-L/2 + ε, 0) : CapSpace m) ((L/2 - ε, 0) : CapSpace m)
  simp only [sub_zero, norm_zero] at hsq
  have hval : dist (toEuclid m ((-L/2 + ε, 0) : CapSpace m))
      (toEuclid m ((L/2 - ε, 0) : CapSpace m)) ^ 2 = (L - 2 * ε) ^ 2 := by
    rw [hsq]; ring
  have hge : L - 2 * ε ≤ dist (toEuclid m ((-L/2 + ε, 0) : CapSpace m))
      (toEuclid m ((L/2 - ε, 0) : CapSpace m)) := by
    nlinarith [dist_nonneg (x := toEuclid m ((-L/2 + ε, 0) : CapSpace m))
      (y := toEuclid m ((L/2 - ε, 0) : CapSpace m)), hval]
  simp only [euclidDiam]
  linarith

/-- **Lower bound for the diameter of the thin domain** (manuscript
`eq:diam-bound`): `L ≤ diam Ω_R` for arbitrary admissible caps. -/
theorem le_euclidDiam_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    L ≤ euclidDiam (thinDomain Cm Cp L R) := by
  have hL0 : 0 < L := span_pos (Cm := Cm) (Cp := Cp) hR hL
  by_contra hcon
  push_neg at hcon
  set D := euclidDiam (thinDomain Cm Cp L R) with hD
  set ε : ℝ := min (L/2) ((L - D)/4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεL : ε ≤ L/2 := min_le_left _ _
  have hεD : ε ≤ (L - D)/4 := min_le_right _ _
  have hlow := sub_le_euclidDiam_thinDomain (Cm := Cm) (Cp := Cp) hR hL hε0 hεL
  rw [← hD] at hlow
  linarith

/-! ## The `L + O(R²)` form -/

/-- The elementary estimate `√(L² + 4R²) ≤ L + 2R²/L` for `L > 0`. -/
theorem sqrt_sq_add_le_add_div (hL0 : 0 < L) (R : ℝ) :
    Real.sqrt (L ^ 2 + 4 * R ^ 2) ≤ L + 2 * R ^ 2 / L := by
  have hdiv : 0 ≤ 2 * R ^ 2 / L := div_nonneg (by positivity) hL0.le
  have hnn : 0 ≤ L + 2 * R ^ 2 / L := by linarith
  have hexp : (L + 2 * R ^ 2 / L) ^ 2 = L ^ 2 + 4 * R ^ 2 + 4 * R ^ 4 / L ^ 2 := by
    field_simp; ring
  have hpos : 0 ≤ 4 * R ^ 4 / L ^ 2 := div_nonneg (by positivity) (by positivity)
  calc Real.sqrt (L ^ 2 + 4 * R ^ 2)
      ≤ Real.sqrt ((L + 2 * R ^ 2 / L) ^ 2) := Real.sqrt_le_sqrt (by rw [hexp]; linarith)
    _ = L + 2 * R ^ 2 / L := Real.sqrt_sq hnn

/-- **The `L + O(R²)` form of the diameter bound** (manuscript `eq:diam-bound`):
`diam Ω_R ≤ L + 2R²/L`. -/
theorem euclidDiam_thinDomain_le_add (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    euclidDiam (thinDomain Cm Cp L R) ≤ L + 2 * R ^ 2 / L :=
  (euclidDiam_thinDomain_le hR hL).trans
    (sqrt_sq_add_le_add_div (span_pos (Cm := Cm) (Cp := Cp) hR hL) R)

/-- **The general diameter bound `eq:diam-bound`**: for arbitrary admissible end
caps the thin domain satisfies `L ≤ diam Ω_R ≤ √(L² + 4R²) ≤ L + 2R²/L`, so
`diam Ω_R = L + O(R²)` as `R → 0`. -/
theorem euclidDiam_thinDomain_bounds (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    L ≤ euclidDiam (thinDomain Cm Cp L R) ∧
      euclidDiam (thinDomain Cm Cp L R) ≤ Real.sqrt (L ^ 2 + 4 * R ^ 2) ∧
      Real.sqrt (L ^ 2 + 4 * R ^ 2) ≤ L + 2 * R ^ 2 / L :=
  ⟨le_euclidDiam_thinDomain hR hL, euclidDiam_thinDomain_le hR hL,
    sqrt_sq_add_le_add_div (span_pos (Cm := Cm) (Cp := Cp) hR hL) R⟩

/-! ## The ambient sup-metric diameter

`CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)` carries the sup metric, for which
the diameter of `Ω_R` is `max L (2R)` up to the same `ε`-approximation; since
`(K₋ + K₊) R < L` and `K₋, K₊ > 0`, this max is `L` as soon as `2R ≤ L`. -/

/-- Sup-metric upper bound: `diam_∞ Ω_R ≤ max L (2R)`. -/
theorem diam_thinDomain_le (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Metric.diam (thinDomain Cm Cp L R) ≤ max L (2 * R) := by
  have hL0 : 0 < L := span_pos (Cm := Cm) (Cp := Cp) hR hL
  refine Metric.diam_le_of_forall_dist_le (le_max_of_le_left hL0.le) ?_
  rintro p ⟨hp1, hp2, hp3⟩ q ⟨hq1, hq2, hq3⟩
  have hpz : ‖p.2‖ < R := lt_of_lt_of_le hp3 (profile_le_R hR hL ⟨hp1, hp2⟩)
  have hqz : ‖q.2‖ < R := lt_of_lt_of_le hq3 (profile_le_R hR hL ⟨hq1, hq2⟩)
  rw [Prod.dist_eq]
  refine max_le (le_max_of_le_left ?_) (le_max_of_le_right ?_)
  · rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  · rw [dist_eq_norm]
    calc ‖p.2 - q.2‖ ≤ ‖p.2‖ + ‖q.2‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith

/-- Sup-metric lower bound: `L ≤ diam_∞ Ω_R` (the same axial witnesses). -/
theorem le_diam_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    L ≤ Metric.diam (thinDomain Cm Cp L R) := by
  have hL0 : 0 < L := span_pos (Cm := Cm) (Cp := Cp) hR hL
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ L/2 →
      L - 2 * ε ≤ Metric.diam (thinDomain Cm Cp L R) := by
    intro ε hε hεL
    have hmem1 : ((-L/2 + ε, 0) : CapSpace m) ∈ thinDomain Cm Cp L R :=
      axialPoint_mem_thinDomain hR hL ⟨by linarith, by linarith⟩
    have hmem2 : ((L/2 - ε, 0) : CapSpace m) ∈ thinDomain Cm Cp L R :=
      axialPoint_mem_thinDomain hR hL ⟨by linarith, by linarith⟩
    have hd := Metric.dist_le_diam_of_mem (isBounded_thinDomain hR hL) hmem1 hmem2
    have hval : dist ((-L/2 + ε, 0) : CapSpace m) ((L/2 - ε, 0) : CapSpace m) = L - 2 * ε := by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [show -L/2 + ε - (L/2 - ε) = -(L - 2 * ε) by ring, abs_neg,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ L - 2 * ε)]
      exact max_eq_left (by linarith)
    linarith [hval ▸ hd]
  by_contra hcon
  push_neg at hcon
  set D := Metric.diam (thinDomain Cm Cp L R) with hD
  set ε : ℝ := min (L/2) ((L - D)/4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεL : ε ≤ L/2 := min_le_left _ _
  have hεD : ε ≤ (L - D)/4 := min_le_right _ _
  have hlow := key ε hε0 hεL
  linarith

end

end Domain
end RobinCaps
