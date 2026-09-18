import Mathlib
import RobinCaps.Cap.Sphere
import RobinCaps.Cap.Sharp

/-!
# The capsule domain and the hemispherical-cap constant `β₀`

Elementary facts needed by the capsule counterexample (manuscript `sec:capsule`,
`cor:counterexample` of `reference/robin_endcaps_corrected_en.tex`):

* `omega_succ_lt_two_mul : ω_{m+1} < 2 ω_m` for `m ≥ 1` (at `m = 0` one has the
  equality `ω₁ = 2 = 2 ω₀`, so the strict inequality genuinely needs `m ≥ 1`);
* the hemispherical-cap constant `beta0 m α = α ω_{m+1} / (2 ω_m)` satisfies
  `0 < β₀ < α` (manuscript `eq:positive-beta`, `eq:hemisphere-beta`);
* `hemisphere_revolutionF_ratio : (α/ω_m) · 𝓕_rev(hemisphere m) = β₀`;
* the capsule `Ω_R = {x : dist(x, S_R) < R}` of total axial span `L` with
  `0 < 2R < L`, where `S_R` is the axial segment of length `L - 2R`
  (manuscript `eq:capsule-domain`), is open, convex, bounded, nonempty and has
  Euclidean diameter exactly `L` (manuscript `eq:exact-diameter`);
* `capsule_eq_union` decomposes the capsule as (open cylinder) ∪ (two open balls
  of radius `R` centred at the endpoints of `S_R`).

We work in `EuclideanSpace ℝ (Fin (m+1))` (so `n = m+1`) with the axis direction
`axis m = EuclideanSpace.single 0 1`, and use mathlib's `Metric.diam` (which is the
Euclidean diameter for this space).
-/

open MeasureTheory Set
open scoped Topology RealInnerProductSpace Pointwise

namespace RobinCaps
namespace Domain

open RobinCaps.Cap

noncomputable section

/-! ## `ω_{m+1} < 2 ω_m` and the constant `β₀` -/

/-- The inductive step: if `ω_{k+1} ≤ 2 ω_k` then `ω_{k+3} < 2 ω_{k+2}`. -/
theorem omega_step_lt (k : ℕ) (h : omega (k + 1) ≤ 2 * omega k) :
    omega (k + 3) < 2 * omega (k + 2) := by
  have h3 : omega (k + 3) = 2 * Real.pi / ((k : ℝ) + 3) * omega (k + 1) := by
    rw [show k + 3 = (k + 1) + 2 by ring, omega_rec (k + 1)]
    push_cast; ring_nf
  rw [h3, omega_rec k]
  have hk := omega_pos k
  have hk1 := omega_pos (k + 1)
  have hpi := Real.pi_pos
  have ha : 0 < 2 * Real.pi / ((k : ℝ) + 3) := by positivity
  have hab : 2 * Real.pi / ((k : ℝ) + 3) < 2 * Real.pi / ((k : ℝ) + 2) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  calc 2 * Real.pi / ((k : ℝ) + 3) * omega (k + 1)
      ≤ 2 * Real.pi / ((k : ℝ) + 3) * (2 * omega k) :=
        mul_le_mul_of_nonneg_left h ha.le
    _ < 2 * Real.pi / ((k : ℝ) + 2) * (2 * omega k) :=
        mul_lt_mul_of_pos_right hab (by positivity)
    _ = 2 * (2 * Real.pi / ((k : ℝ) + 2) * omega k) := by ring

/-- `ω_{m+1} ≤ 2 ω_m` for every `m` (with equality exactly at `m = 0`). -/
theorem omega_succ_le_two_mul (m : ℕ) : omega (m + 1) ≤ 2 * omega m := by
  have key : ∀ m : ℕ, omega (m + 1) ≤ 2 * omega m ∧ omega (m + 2) ≤ 2 * omega (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [omega_one, omega_zero]; norm_num
      · rw [omega_two, omega_one]; linarith [Real.pi_le_four]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have := omega_step_lt k ih.1
      rw [show k + 3 = k + 1 + 2 by ring] at this
      exact this.le
  exact (key m).1

/-- `ω_{m+1} > 0`. -/
theorem omega_succ_pos (m : ℕ) : 0 < omega (m + 1) := omega_pos (m + 1)

/-- **`ω_{m+1} < 2 ω_m` for `m ≥ 1`.**  (`ω₂ = π < 4`, `ω₃ = 4π/3 < 2π`, …) -/
theorem omega_succ_lt_two_mul (m : ℕ) (hm : 1 ≤ m) : omega (m + 1) < 2 * omega m := by
  rcases Nat.exists_eq_add_of_le' hm with ⟨k, rfl⟩
  rcases k with _ | k
  · simp only [zero_add]
    rw [omega_two, omega_one]; linarith [Real.pi_lt_four]
  · have := omega_step_lt k (omega_succ_le_two_mul k)
    rw [show k + 3 = k + 1 + 1 + 1 by ring, show k + 2 = k + 1 + 1 by ring] at this
    exact this

/-- The hemispherical-cap constant `β₀ = α ω_{m+1} / (2 ω_m)`
(manuscript `eq:positive-beta`, `eq:hemisphere-beta`). -/
def beta0 (m : ℕ) (α : ℝ) : ℝ := α * omega (m + 1) / (2 * omega m)

/-- `β₀ > 0` for `α > 0`. -/
theorem beta0_pos {m : ℕ} {α : ℝ} (hα : 0 < α) : 0 < beta0 m α := by
  unfold beta0
  have := omega_pos m
  have := omega_pos (m + 1)
  positivity

/-- `β₀ < α` for `α > 0` and `m ≥ 1`. -/
theorem beta0_lt {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) : beta0 m α < α := by
  unfold beta0
  have h2 : 0 < 2 * omega m := by have := omega_pos m; positivity
  rw [div_lt_iff₀ h2]
  have := omega_succ_lt_two_mul m hm
  calc α * omega (m + 1) < α * (2 * omega m) := by
        exact mul_lt_mul_of_pos_left this hα
    _ = α * (2 * omega m) := rfl

/-- `(α / ω_m) · 𝓕_rev(hemisphere m) = β₀` (the explicit revolution functional). -/
theorem hemisphere_revolutionF_ratio (m : ℕ) (hm : 1 ≤ m) (α : ℝ) :
    α / omega m * (hemisphere m).revolutionF = beta0 m α := by
  rw [hemisphere_revolutionF_eq m hm, beta0]
  have := omega_ne_zero m
  field_simp

/-! ## The capsule domain -/

variable {m : ℕ}

/-- The axial unit vector `e = (1, 0, …, 0)` of `ℝ^{m+1}`. -/
def axis (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single 0 1

@[simp] theorem norm_axis : ‖axis m‖ = 1 := by
  simp [axis]

@[simp] theorem inner_axis_self : ⟪axis m, axis m⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_axis]; norm_num

theorem norm_smul_axis (t : ℝ) : ‖t • axis m‖ = |t| := by
  rw [norm_smul, norm_axis, mul_one, Real.norm_eq_abs]

/-- The central axial segment `S_R = [-(L/2 - R), L/2 - R] · e` of length `L - 2R`. -/
def axisSegment (m : ℕ) (L R : ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  segment ℝ ((-(L / 2 - R)) • axis m) ((L / 2 - R) • axis m)

/-- The capsule `Ω_R = {x : dist(x, S_R) < R}` (manuscript `eq:capsule-domain`). -/
def capsule (m : ℕ) (L R : ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | Metric.infDist x (axisSegment m L R) < R}

theorem axisSegment_nonempty (L R : ℝ) : (axisSegment m L R).Nonempty :=
  ⟨_, left_mem_segment ℝ _ _⟩

theorem convex_axisSegment (L R : ℝ) : Convex ℝ (axisSegment m L R) :=
  convex_segment _ _

theorem left_mem_axisSegment (L R : ℝ) : (-(L / 2 - R)) • axis m ∈ axisSegment m L R :=
  left_mem_segment ℝ _ _

theorem right_mem_axisSegment (L R : ℝ) : (L / 2 - R) • axis m ∈ axisSegment m L R :=
  right_mem_segment ℝ _ _

/-- The axial segment as the image of an interval. -/
theorem axisSegment_eq_image {L R : ℝ} (h : 2 * R ≤ L) :
    axisSegment m L R = (fun t : ℝ => t • axis m) '' Icc (-(L / 2 - R)) (L / 2 - R) := by
  have := image_segment ℝ (LinearMap.toSpanSingleton ℝ _ (axis m)).toAffineMap
    (-(L / 2 - R)) (L / 2 - R)
  rw [segment_eq_Icc (by linarith)] at this
  simp only [LinearMap.coe_toAffineMap, LinearMap.toSpanSingleton_apply] at this
  rw [axisSegment, ← this]

theorem smul_axis_mem_axisSegment {L R t : ℝ} (h : 2 * R ≤ L) (ht : |t| ≤ L / 2 - R) :
    t • axis m ∈ axisSegment m L R := by
  rw [axisSegment_eq_image h]
  exact ⟨t, abs_le.mp ht, rfl⟩

theorem mem_axisSegment_iff {L R : ℝ} (h : 2 * R ≤ L) {p : EuclideanSpace ℝ (Fin (m + 1))} :
    p ∈ axisSegment m L R ↔ ∃ t, |t| ≤ L / 2 - R ∧ p = t • axis m := by
  rw [axisSegment_eq_image h]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, abs_le.mpr ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, abs_le.mp ht, rfl⟩

/-- Points of the axial segment have norm at most `L/2 - R`. -/
theorem norm_le_of_mem_axisSegment {L R : ℝ} (h : 2 * R ≤ L)
    {p : EuclideanSpace ℝ (Fin (m + 1))} (hp : p ∈ axisSegment m L R) :
    ‖p‖ ≤ L / 2 - R := by
  have hc : 0 ≤ L / 2 - R := by linarith
  have h1 : (-(L / 2 - R)) • axis m ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1)))
      (L / 2 - R) := by
    rw [mem_closedBall_zero_iff, norm_smul_axis, abs_neg, abs_of_nonneg hc]
  have h2 : (L / 2 - R) • axis m ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1)))
      (L / 2 - R) := by
    rw [mem_closedBall_zero_iff, norm_smul_axis, abs_of_nonneg hc]
  have := (convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) (L / 2 - R)).segment_subset
    h1 h2 hp
  rwa [mem_closedBall_zero_iff] at this

/-- Membership in the capsule: some point of the segment is within distance `< R`. -/
theorem mem_capsule_iff {L R : ℝ} {x : EuclideanSpace ℝ (Fin (m + 1))} :
    x ∈ capsule m L R ↔ ∃ p ∈ axisSegment m L R, dist x p < R := by
  unfold capsule
  rw [mem_setOf_eq, Metric.infDist_lt_iff (axisSegment_nonempty L R)]

/-- The capsule is the union of the open balls of radius `R` centred on the segment. -/
theorem capsule_eq_biUnion (L R : ℝ) :
    capsule m L R = ⋃ p ∈ axisSegment m L R, Metric.ball p R := by
  ext x
  simp only [mem_capsule_iff, mem_iUnion, Metric.mem_ball, exists_prop]

/-- The capsule is the Minkowski sum of the segment and the open ball `B(0,R)`. -/
theorem capsule_eq_add (L R : ℝ) :
    capsule m L R = axisSegment m L R + Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) R := by
  ext x
  rw [mem_capsule_iff, Set.mem_add]
  constructor
  · rintro ⟨p, hp, hd⟩
    refine ⟨p, hp, x - p, ?_, add_sub_cancel p x⟩
    rwa [mem_ball_zero_iff, ← dist_eq_norm]
  · rintro ⟨p, hp, b, hb, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.mp hb

theorem isOpen_capsule (L R : ℝ) : IsOpen (capsule m L R) := by
  rw [capsule_eq_biUnion]
  exact isOpen_biUnion fun _ _ => Metric.isOpen_ball

theorem convex_capsule (L R : ℝ) : Convex ℝ (capsule m L R) := by
  rw [capsule_eq_add]
  exact (convex_axisSegment L R).add (convex_ball 0 R)

theorem capsule_nonempty {L R : ℝ} (hR : 0 < R) : (capsule m L R).Nonempty :=
  ⟨_, mem_capsule_iff.mpr ⟨_, left_mem_axisSegment L R, by rw [dist_self]; exact hR⟩⟩

/-- The capsule is contained in the open ball of radius `L/2`. -/
theorem capsule_subset_ball {L R : ℝ} (h : 2 * R ≤ L) :
    capsule m L R ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) (L / 2) := by
  intro x hx
  obtain ⟨p, hp, hd⟩ := mem_capsule_iff.mp hx
  have hp' := norm_le_of_mem_axisSegment h hp
  rw [mem_ball_zero_iff]
  calc ‖x‖ = ‖(x - p) + p‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le _ _
    _ < R + (L / 2 - R) := by rw [← dist_eq_norm]; exact add_lt_add_of_lt_of_le hd hp'
    _ = L / 2 := by ring

theorem isBounded_capsule {L R : ℝ} (h : 2 * R ≤ L) :
    Bornology.IsBounded (capsule m L R) :=
  Metric.isBounded_ball.subset (capsule_subset_ball h)

/-- Upper bound `diam Ω_R ≤ L`. -/
theorem diam_capsule_le {L R : ℝ} (hR : 0 < R) (h : 2 * R ≤ L) :
    Metric.diam (capsule m L R) ≤ L := by
  calc Metric.diam (capsule m L R)
      ≤ Metric.diam (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) (L / 2)) :=
        Metric.diam_mono (capsule_subset_ball h) Metric.isBounded_ball
    _ ≤ 2 * (L / 2) := Metric.diam_ball (by linarith)
    _ = L := by ring

/-- The near-endpoint axial points `±(L/2 - ε) e` lie in the capsule for `0 < ε < R`. -/
theorem smul_axis_mem_capsule_of_lt {L R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    (L / 2 - ε) • axis m ∈ capsule m L R ∧ (-(L / 2 - ε)) • axis m ∈ capsule m L R := by
  constructor
  · refine mem_capsule_iff.mpr ⟨_, right_mem_axisSegment L R, ?_⟩
    rw [dist_eq_norm, ← sub_smul, norm_smul_axis]
    rw [show L / 2 - ε - (L / 2 - R) = R - ε by ring, abs_of_pos (by linarith)]
    linarith
  · refine mem_capsule_iff.mpr ⟨_, left_mem_axisSegment L R, ?_⟩
    rw [dist_eq_norm, ← sub_smul, norm_smul_axis]
    rw [show -(L / 2 - ε) - -(L / 2 - R) = -(R - ε) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith

/-- Lower bound `L - 2ε ≤ diam Ω_R` for every `0 < ε < R`. -/
theorem sub_le_diam_capsule {L R ε : ℝ} (hL : 2 * R ≤ L) (hε : 0 < ε) (hεR : ε < R) :
    L - 2 * ε ≤ Metric.diam (capsule m L R) := by
  obtain ⟨h1, h2⟩ := smul_axis_mem_capsule_of_lt (m := m) (L := L) hε hεR
  have := Metric.dist_le_diam_of_mem (isBounded_capsule hL) h1 h2
  rw [dist_eq_norm, ← sub_smul, norm_smul_axis,
    show L / 2 - ε - -(L / 2 - ε) = L - 2 * ε by ring,
    abs_of_nonneg (by linarith)] at this
  exact this

/-- **Exact diameter of the capsule** (manuscript `eq:exact-diameter`):
`diam Ω_R = L` whenever `0 < R` and `2R < L`. -/
theorem diam_capsule {L R : ℝ} (hR : 0 < R) (hL : 2 * R < L) :
    Metric.diam (capsule m L R) = L := by
  refine le_antisymm (diam_capsule_le hR hL.le) ?_
  by_contra hcon
  push_neg at hcon
  set D := Metric.diam (capsule m L R) with hD
  set ε : ℝ := min (R / 2) ((L - D) / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεR : ε < R := (min_le_left _ _).trans_lt (by linarith)
  have hεD : ε ≤ (L - D) / 4 := min_le_right _ _
  have := sub_le_diam_capsule (m := m) hL.le hε0 hεR
  rw [← hD] at this
  linarith

/-! ## Decomposition into a cylinder and two end balls -/

/-- The open cylinder body `{x : |x·e| < L/2 - R, ‖x - (x·e) e‖ < R}`. -/
def cylinder (m : ℕ) (L R : ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | |⟪x, axis m⟫| < L / 2 - R ∧ ‖x - ⟪x, axis m⟫ • axis m‖ < R}

/-- Pythagoras along the axis: `‖x - t e‖² = ‖x - (x·e) e‖² + ((x·e) - t)²`. -/
theorem norm_sub_smul_axis_sq (x : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    ‖x - t • axis m‖ ^ 2 = ‖x - ⟪x, axis m⟫ • axis m‖ ^ 2 + (⟪x, axis m⟫ - t) ^ 2 := by
  set s := ⟪x, axis m⟫ with hs
  have hdecomp : x - t • axis m = (x - s • axis m) + (s - t) • axis m := by
    rw [sub_smul]; abel
  rw [hdecomp, norm_add_sq_real]
  have hinner : ⟪x - s • axis m, (s - t) • axis m⟫ = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_smul_left, inner_axis_self]
    simp [hs]
  rw [hinner, norm_smul_axis, sq_abs]
  ring

/-- **The capsule is the union of the open cylinder and the two end balls.** -/
theorem capsule_eq_union {L R : ℝ} (hR : 0 < R) (hL : 2 * R < L) :
    capsule m L R =
      cylinder m L R ∪ Metric.ball ((L / 2 - R) • axis m) R ∪
        Metric.ball ((-(L / 2 - R)) • axis m) R := by
  ext x
  set c := L / 2 - R with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set s := ⟪x, axis m⟫ with hs
  constructor
  · intro hx
    obtain ⟨p, hp, hd⟩ := mem_capsule_iff.mp hx
    obtain ⟨t, ht, rfl⟩ := (mem_axisSegment_iff hL.le).mp hp
    rw [← hc] at ht
    rw [dist_eq_norm] at hd
    have hsq := norm_sub_smul_axis_sq x t
    rw [← hs] at hsq
    have hdsq : ‖x - t • axis m‖ ^ 2 < R ^ 2 := by
      have := norm_nonneg (x - t • axis m)
      nlinarith
    rw [hsq] at hdsq
    obtain ⟨ht1, ht2⟩ := abs_le.mp ht
    rcases lt_or_ge |s| c with hsc | hsc
    · left; left
      refine ⟨hsc, ?_⟩
      have hn := norm_nonneg (x - s • axis m)
      nlinarith
    · rcases le_or_gt 0 s with hs0 | hs0
      · -- s ≥ c: the right end ball
        left; right
        rw [abs_of_nonneg hs0] at hsc
        rw [Metric.mem_ball, dist_eq_norm]
        have h2 := norm_sub_smul_axis_sq x c
        rw [← hs] at h2
        have hn := norm_nonneg (x - c • axis m)
        have hn' := norm_nonneg (x - s • axis m)
        have hle : (s - c) ^ 2 ≤ (s - t) ^ 2 := by nlinarith
        nlinarith
      · -- s ≤ -c: the left end ball
        right
        rw [abs_of_neg hs0] at hsc
        rw [Metric.mem_ball, dist_eq_norm]
        have h2 := norm_sub_smul_axis_sq x (-c)
        rw [← hs] at h2
        have hn := norm_nonneg (x - (-c) • axis m)
        have hn' := norm_nonneg (x - s • axis m)
        have hle : (s - -c) ^ 2 ≤ (s - t) ^ 2 := by nlinarith
        nlinarith
  · rintro ((⟨h1, h2⟩ | h) | h)
    · -- cylinder: project onto the axis
      refine mem_capsule_iff.mpr ⟨s • axis m, ?_, ?_⟩
      · exact smul_axis_mem_axisSegment hL.le (by rw [← hc]; exact h1.le)
      · rw [dist_eq_norm]; exact h2
    · exact mem_capsule_iff.mpr ⟨_, right_mem_axisSegment L R, by rw [← hc]; exact h⟩
    · exact mem_capsule_iff.mpr ⟨_, left_mem_axisSegment L R, by rw [← hc]; exact h⟩

/-- The cylinder and the end balls are contained in the capsule (the `⊇` inclusion). -/
theorem union_subset_capsule {L R : ℝ} (hR : 0 < R) (hL : 2 * R < L) :
    cylinder m L R ∪ Metric.ball ((L / 2 - R) • axis m) R ∪
        Metric.ball ((-(L / 2 - R)) • axis m) R ⊆ capsule m L R :=
  (capsule_eq_union hR hL).symm.subset

end

end Domain
end RobinCaps
