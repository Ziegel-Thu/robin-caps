import Mathlib
import RobinCaps.Domain.Thin
import RobinCaps.Cap.Append

/-!
# Convexity of the thin domain `Ω_R`

The manuscript (`sec:setup`, just after `eq:domain`) asserts that

> `Ω_R` is a nonempty bounded convex open set, hence a Lipschitz domain.

`RobinCaps/Domain/Thin.lean` proves nonemptiness, boundedness and openness but
explicitly leaves convexity open.  This file supplies it.

## Strategy

The radial profile `r_R` of `eq:profile` is the *pointwise minimum* of the two
one-sided glued profiles

* `x ↦ R · appendθ C₋ ((-L/2 - x)/R)` — the left cap continued by the constant
  `R` to the right of the left interface,
* `x ↦ R · appendθ C₊ ((x - L/2)/R)` — the right cap continued by the constant
  `R` to the left of the right interface,

where `Cap.appendθ` is the glued profile of `RobinCaps/Cap/Append.lean`
(constant `1` on `(-∞, -K]`, `θ` on `(-K, ∞)`).  This is
`profile_eq_min`, and it uses the admissibility hypothesis
`(K₋ + K₊) R < L` (the two interfaces are ordered) together with `θ ≤ 1`.

Each of the two pieces is concave: `Cap.appendθ_concaveOn` — whose junction
argument `Cap.appendθ_junction` is exactly the "cap side approaches `1` at the
entrance" limit — composed with an affine reparametrisation (`concaveOn_comp_affine`,
with the reflection `x ↦ (-L/2 - x)/R` on the left) and scaled by `R > 0`.
The minimum of two concave functions is concave (`concaveOn_min`), so `r_R`
is concave on `(-L/2, L/2)` (`concaveOn_profile`).

Finally a solid of revolution `{p | p.1 ∈ I, ‖p.2‖ < f p.1}` over a concave
radius `f` on a convex `I` is convex (`convex_of_concave_radius`), whence
`convex_thinDomain`.

## Main results

* `concaveOn_profile`: `r_R` is concave on `(-L/2, L/2)`;
* `convex_of_concave_radius`: the general revolution criterion;
* `convex_thinDomain`: **`Ω_R` is convex**;
* `convex_thinDomain_hemisphere`: the hemispherical (capsule) case.
-/

open Set

namespace RobinCaps
namespace Domain

open RobinCaps.Cap

noncomputable section

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## Two general convexity lemmas -/

/-- Precomposition with an affine map `x ↦ c x + d` preserves concavity. -/
theorem concaveOn_comp_affine {g φ : ℝ → ℝ} {J I : Set ℝ} {c d : ℝ}
    (hg : ConcaveOn ℝ J g) (hI : Convex ℝ I) (hφ : ∀ x, φ x = c * x + d)
    (hmaps : ∀ x ∈ I, φ x ∈ J) :
    ConcaveOn ℝ I (fun x => g (φ x)) := by
  refine ⟨hI, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hg.2 (hmaps x hx) (hmaps y hy) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : φ (a * x + b * y) = a * φ x + b * φ y := by
    simp only [hφ]
    rw [show a * (c * x + d) + b * (c * y + d) = c * (a * x + b * y) + (a + b) * d from by ring,
      hab, one_mul]
  rw [he]
  exact h

/-- The pointwise minimum of two concave functions is concave. -/
theorem concaveOn_min {f g : ℝ → ℝ} {I : Set ℝ} (hf : ConcaveOn ℝ I f)
    (hg : ConcaveOn ℝ I g) : ConcaveOn ℝ I (fun x => min (f x) (g x)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h1 := hf.2 hx hy ha hb hab
  have h2 := hg.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h1 h2 ⊢
  have e1 : a * min (f x) (g x) + b * min (f y) (g y) ≤ a * f x + b * f y :=
    add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
  have e2 : a * min (f x) (g x) + b * min (f y) (g y) ≤ a * g x + b * g y :=
    add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
  exact le_min (e1.trans h1) (e2.trans h2)

/-! ## The two one-sided glued profiles -/

/-- The left cap profile continued by the constant `R` past the left interface:
`R · appendθ C₋` reparametrised by the reflection `x ↦ (-L/2 - x)/R`. -/
def leftHalfProfile (Cm : Cap m) (L R : ℝ) (x : ℝ) : ℝ := R * appendθ Cm ((-L/2 - x) / R)

/-- The right cap profile continued by the constant `R` before the right
interface: `R · appendθ C₊` reparametrised by `x ↦ (x - L/2)/R`. -/
def rightHalfProfile (Cp : Cap m) (L R : ℝ) (x : ℝ) : ℝ := R * appendθ Cp ((x - L/2) / R)

/-- The reflected reparametrisation maps `(-L/2, L/2)` into `(-L/R, 0)`. -/
theorem left_full_param_mem (hR : 0 < R) {x : ℝ} (hx : x ∈ Ioo (-L/2) (L/2)) :
    (-L/2 - x) / R ∈ Ioo (-(L/R)) 0 := by
  have hLR : (L / R) * R = L := div_mul_cancel₀ L hR.ne'
  constructor
  · rw [lt_div_iff₀ hR]; linarith [hx.2]
  · rw [div_lt_iff₀ hR]; linarith [hx.1]

/-- The right reparametrisation maps `(-L/2, L/2)` into `(-L/R, 0)`. -/
theorem right_full_param_mem (hR : 0 < R) {x : ℝ} (hx : x ∈ Ioo (-L/2) (L/2)) :
    (x - L/2) / R ∈ Ioo (-(L/R)) 0 := by
  have hLR : (L / R) * R = L := div_mul_cancel₀ L hR.ne'
  constructor
  · rw [lt_div_iff₀ hR]; linarith [hx.1]
  · rw [div_lt_iff₀ hR]; linarith [hx.2]

/-- **The left half-profile is concave** on the whole axial interval. -/
theorem concaveOn_leftHalfProfile (hR : 0 < R) :
    ConcaveOn ℝ (Ioo (-L/2) (L/2)) (leftHalfProfile Cm L R) := by
  have hbase : ConcaveOn ℝ (Ioo (-(L/R)) 0) (appendθ Cm) := by
    have h := appendθ_concaveOn Cm (L/R - Cm.K)
    rwa [show Cm.K + (L/R - Cm.K) = L/R from by ring] at h
  have hcomp : ConcaveOn ℝ (Ioo (-L/2) (L/2))
      (fun x => appendθ Cm ((-L/2 - x) / R)) :=
    concaveOn_comp_affine (c := -(1/R)) (d := -L/2/R) hbase (convex_Ioo _ _)
      (fun x => by ring) (fun x hx => left_full_param_mem hR hx)
  have h := hcomp.smul (c := R) hR.le
  simpa only [smul_eq_mul, leftHalfProfile] using h

/-- **The right half-profile is concave** on the whole axial interval. -/
theorem concaveOn_rightHalfProfile (hR : 0 < R) :
    ConcaveOn ℝ (Ioo (-L/2) (L/2)) (rightHalfProfile Cp L R) := by
  have hbase : ConcaveOn ℝ (Ioo (-(L/R)) 0) (appendθ Cp) := by
    have h := appendθ_concaveOn Cp (L/R - Cp.K)
    rwa [show Cp.K + (L/R - Cp.K) = L/R from by ring] at h
  have hcomp : ConcaveOn ℝ (Ioo (-L/2) (L/2))
      (fun x => appendθ Cp ((x - L/2) / R)) :=
    concaveOn_comp_affine (c := 1/R) (d := -(L/2/R)) hbase (convex_Ioo _ _)
      (fun x => by ring) (fun x hx => right_full_param_mem hR hx)
  have h := hcomp.smul (c := R) hR.le
  simpa only [smul_eq_mul, rightHalfProfile] using h

/-! ## The profile as a minimum -/

/-- **The profile is the pointwise minimum of the two half-profiles.** -/
theorem profile_eq_min (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : x ∈ Ioo (-L/2) (L/2)) :
    profile Cm Cp L R x = min (leftHalfProfile Cm L R x) (rightHalfProfile Cp L R x) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  simp only [leftHalfProfile, rightHalfProfile]
  rcases lt_or_ge x (-L/2 + Cm.K * R) with h | h
  · -- inside the left cap: the left half-profile is the smaller one
    have hsm : -Cm.K < (-L/2 - x) / R := by rw [lt_div_iff₀ hR]; linarith
    have hsp : (x - L/2) / R ≤ -Cp.K := by rw [div_le_iff₀ hR]; linarith
    rw [profile_left h, appendθ_of_lt Cm hsm, appendθ_of_le Cp hsp, mul_one]
    have hle : Cm.θ ((-L/2 - x) / R) ≤ 1 := Cm.θ_le_one _ (left_param_mem hR ⟨hx.1, h⟩)
    exact (min_eq_left (by nlinarith)).symm
  · rcases le_or_gt x (L/2 - Cp.K * R) with h' | h'
    · -- the bulk: both half-profiles equal `R`
      have hsm : (-L/2 - x) / R ≤ -Cm.K := by rw [div_le_iff₀ hR]; linarith
      have hsp : (x - L/2) / R ≤ -Cp.K := by rw [div_le_iff₀ hR]; linarith
      rw [profile_bulk h h', appendθ_of_le Cm hsm, appendθ_of_le Cp hsp]
      simp
    · -- inside the right cap: the right half-profile is the smaller one
      have hsm : (-L/2 - x) / R ≤ -Cm.K := by rw [div_le_iff₀ hR]; linarith
      have hsp : -Cp.K < (x - L/2) / R := by rw [lt_div_iff₀ hR]; linarith
      rw [profile_right h h', appendθ_of_le Cm hsm, appendθ_of_lt Cp hsp, mul_one]
      have hle : Cp.θ ((x - L/2) / R) ≤ 1 := Cp.θ_le_one _ (right_param_mem hR ⟨h', hx.2⟩)
      exact (min_eq_right (by nlinarith)).symm

/-! ## Concavity of the profile -/

/-- **The radial profile `r_R` is concave on the axial interval `(-L/2, L/2)`.**

This is the analytic content of the manuscript's claim that `Ω_R` is convex
(`sec:setup`, after `eq:domain`). -/
theorem concaveOn_profile (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ConcaveOn ℝ (Ioo (-L/2) (L/2)) (profile Cm Cp L R) := by
  have hmin := concaveOn_min (concaveOn_leftHalfProfile (Cm := Cm) (L := L) (R := R) hR)
    (concaveOn_rightHalfProfile (Cp := Cp) (L := L) (R := R) hR)
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmem : a • x + b • y ∈ Ioo (-L/2) (L/2) := convex_Ioo _ _ hx hy ha hb hab
  rw [profile_eq_min hR hL hx, profile_eq_min hR hL hy, profile_eq_min hR hL hmem]
  exact hmin.2 hx hy ha hb hab

/-! ## Solids of revolution over a concave radius -/

/-- **A solid of revolution with concave radial profile is convex.**

If `f` is concave on a convex set `I ⊆ ℝ`, then
`{(x, z) : x ∈ I, ‖z‖ < f x}` is convex.  The proof is the triangle inequality
`‖a z₁ + b z₂‖ ≤ a‖z₁‖ + b‖z₂‖` followed by the chord inequality for `f`. -/
theorem convex_of_concave_radius {f : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hf : ConcaveOn ℝ I f) :
    Convex ℝ {p : CapSpace m | p.1 ∈ I ∧ ‖p.2‖ < f p.1} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have hfst : (a • p + b • q).1 = a * p.1 + b * q.1 := by simp
  have hsnd : (a • p + b • q).2 = a • p.2 + b • q.2 := by simp
  have hmemI : a * p.1 + b * q.1 ∈ I := by
    have := hI hp1 hq1 ha hb hab
    simpa using this
  refine ⟨by rw [hfst]; exact hmemI, ?_⟩
  rw [hfst, hsnd]
  have hconc := hf.2 hp1 hq1 ha hb hab
  simp only [smul_eq_mul] at hconc
  have hnorm : ‖a • p.2 + b • q.2‖ ≤ a * ‖p.2‖ + b * ‖q.2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hb]
  have hstrict : a * ‖p.2‖ + b * ‖q.2‖ < a * f p.1 + b * f q.1 := by
    rcases ha.lt_or_eq with ha' | ha'
    · have h1 : a * ‖p.2‖ < a * f p.1 := by nlinarith
      have h2 : b * ‖q.2‖ ≤ b * f q.1 := by nlinarith
      linarith
    · have hb1 : b = 1 := by rw [← ha'] at hab; linarith
      rw [← ha', hb1]
      simpa using hq2
  linarith

/-! ## Convexity of `Ω_R` -/

/-- **The thin domain `Ω_R` is convex** (manuscript `sec:setup`: "`Ω_R` is a
nonempty bounded convex open set, hence a Lipschitz domain"). -/
theorem convex_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Convex ℝ (thinDomain Cm Cp L R) := by
  have heq : thinDomain Cm Cp L R =
      {p : CapSpace m | p.1 ∈ Ioo (-L/2) (L/2) ∧ ‖p.2‖ < profile Cm Cp L R p.1} := by
    ext p
    simp [thinDomain, mem_Ioo, and_assoc]
  rw [heq]
  exact convex_of_concave_radius (convex_Ioo _ _) (concaveOn_profile hR hL)

/-- **The hemispherical thin domain (the Euclidean capsule) is convex.** -/
theorem convex_thinDomain_hemisphere (hR : 0 < R) (hL : 2 * R < L) :
    Convex ℝ (thinDomain (hemisphere m) (hemisphere m) L R) := by
  refine convex_thinDomain hR ?_
  show ((1 : ℝ) + 1) * R < L
  linarith

end

end Domain
end RobinCaps
