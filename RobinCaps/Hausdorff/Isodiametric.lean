import RobinCaps.Hausdorff.IsodiamIface

/-!
# Isodiametric inequality via Steiner symmetrisation

This file proves `isodiametric_iso`, the isodiametric inequality

  `volume A ≤ volume (closedBall 0 (diam A / 2))`

for compact `A ⊆ ℝ^m`, from the four Steiner symmetrisation properties stated as hypotheses in
`RobinCaps.Hausdorff.IsodiamIface` (`SteinerCompactProp`, `SteinerVolumeProp`, `SteinerDiamProp`,
`SteinerSymmProp`).

## Strategy

We symmetrise `A` successively in the coordinate directions `0, 1, …, m-1`, obtaining
`Aₖ := symmUpTo_iso m A k` (`A₀ = A`). By induction each `Aₖ` is compact, has the same volume as
`A`, has diameter `≤ diam A`, and is invariant under `reflE j` (reflection in coordinate `j`) for
every `j < k`. Hence `A* := Aₘ` is invariant under every coordinate reflection.

Applying all `m` coordinate reflections successively to a point `x ∈ A*` negates every
coordinate, so `-x ∈ A*` as well (`negFirst_iso` interpolates between `x` and `-x` one coordinate
at a time and stays inside `A*` throughout, by the invariance above). Since `A*` is compact
(hence bounded), `2‖x‖ = dist x (-x) ≤ diam A* ≤ diam A`, so `A* ⊆ closedBall 0 (diam A / 2)`.
Finally `volume A = volume A* ≤ volume (closedBall 0 (diam A / 2))` by monotonicity of `volume`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-! ## Iterated Steiner symmetrisation -/

/-- Iterated Steiner symmetrisation of `A` in coordinates `0, 1, …, k - 1`. -/
noncomputable def symmUpTo_iso (m : ℕ) (A : Set (EuclideanSpace ℝ (Fin m))) :
    ℕ → Set (EuclideanSpace ℝ (Fin m)) :=
  fun k => Nat.rec A (fun k Ak => if h : k < m then steinerSym ⟨k, h⟩ Ak else Ak) k

theorem symmUpTo_zero_iso (m : ℕ) (A : Set (EuclideanSpace ℝ (Fin m))) :
    symmUpTo_iso m A 0 = A := rfl

theorem symmUpTo_succ_iso (m : ℕ) (A : Set (EuclideanSpace ℝ (Fin m))) (k : ℕ) :
    symmUpTo_iso m A (k + 1) =
      if h : k < m then steinerSym ⟨k, h⟩ (symmUpTo_iso m A k) else symmUpTo_iso m A k := rfl

theorem isCompact_symmUpTo_iso (m : ℕ) (hC : SteinerCompactProp m)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A) (k : ℕ) :
    IsCompact (symmUpTo_iso m A k) := by
  induction k with
  | zero => rw [symmUpTo_zero_iso]; exact hA
  | succ k ih =>
      rw [symmUpTo_succ_iso]
      split_ifs with h
      · exact hC _ _ ih
      · exact ih

theorem volume_symmUpTo_iso (m : ℕ) (hC : SteinerCompactProp m) (hV : SteinerVolumeProp m)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A) (k : ℕ) :
    volume (symmUpTo_iso m A k) = volume A := by
  induction k with
  | zero => rw [symmUpTo_zero_iso]
  | succ k ih =>
      rw [symmUpTo_succ_iso]
      split_ifs with h
      · rw [hV _ _ (isCompact_symmUpTo_iso m hC hA k), ih]
      · exact ih

theorem diam_symmUpTo_iso (m : ℕ) (hC : SteinerCompactProp m) (hD : SteinerDiamProp m)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A) (k : ℕ) :
    diam (symmUpTo_iso m A k) ≤ diam A := by
  induction k with
  | zero => rw [symmUpTo_zero_iso]
  | succ k ih =>
      rw [symmUpTo_succ_iso]
      split_ifs with h
      · exact (hD _ _ (isCompact_symmUpTo_iso m hC hA k)).trans ih
      · exact ih

/-- Every `Aₖ` is invariant under `reflE j` for `j < k` (the previously-symmetrised
coordinates). -/
theorem reflE_mem_symmUpTo_iso (m : ℕ) (hC : SteinerCompactProp m) (hS : SteinerSymmProp m)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A) (k : ℕ) :
    ∀ j : Fin m, (j : ℕ) < k → ∀ x ∈ symmUpTo_iso m A k, reflE j x ∈ symmUpTo_iso m A k := by
  induction k with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
      intro j hj x hx
      by_cases hkm : k < m
      · rw [symmUpTo_succ_iso, dif_pos hkm] at hx ⊢
        have hAk : IsCompact (symmUpTo_iso m A k) := isCompact_symmUpTo_iso m hC hA k
        have hSk := hS ⟨k, hkm⟩ (symmUpTo_iso m A k) hAk
        rcases lt_or_ge (j : ℕ) k with hjk | hjk
        · have hjne : j ≠ (⟨k, hkm⟩ : Fin m) := by
            intro he
            have : (j : ℕ) = k := congrArg Fin.val he
            omega
          exact hSk.2 j hjne (ih j hjk) x hx
        · have hjeq : j = (⟨k, hkm⟩ : Fin m) := by
            apply Fin.ext
            show (j : ℕ) = k
            omega
          rw [hjeq]
          exact hSk.1 x hx
      · rw [symmUpTo_succ_iso, dif_neg hkm] at hx ⊢
        have hjk : (j : ℕ) < k := by
          have := j.isLt
          omega
        exact ih j hjk x hx

/-! ## Negating coordinates one at a time -/

/-- `x` with its first `k` coordinates negated and the rest left unchanged. -/
noncomputable def negFirst_iso (m k : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j : Fin m => if (j : ℕ) < k then -(x j) else x j)

theorem negFirst_apply_iso (m k : ℕ) (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    negFirst_iso m k x j = if (j : ℕ) < k then -(x j) else x j := rfl

theorem reflE_apply_iso (m : ℕ) (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    reflE i x j = if j = i then -(x i) else x j := by
  simp only [reflE, updE, PiLp.toLp_apply, Function.update_apply]

theorem negFirst_zero_iso (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    negFirst_iso m 0 x = x := by
  apply PiLp.ext
  intro j
  rw [negFirst_apply_iso]
  simp

theorem negFirst_succ_iso (m k : ℕ) (h : k < m) (x : EuclideanSpace ℝ (Fin m)) :
    negFirst_iso m (k + 1) x = reflE ⟨k, h⟩ (negFirst_iso m k x) := by
  apply PiLp.ext
  intro j
  simp only [negFirst_apply_iso, reflE_apply_iso]
  by_cases hjk : (j : ℕ) = k
  · have hjeq : j = (⟨k, h⟩ : Fin m) := Fin.ext hjk
    simp [hjeq]
  · have hjne : j ≠ (⟨k, h⟩ : Fin m) := fun he => hjk (congrArg Fin.val he)
    have hiff : (j : ℕ) < k + 1 ↔ (j : ℕ) < k := by omega
    simp [hjne, hiff]

theorem negFirst_eq_neg_iso (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    negFirst_iso m m x = -x := by
  apply PiLp.ext
  intro j
  rw [negFirst_apply_iso, PiLp.neg_apply, if_pos j.isLt]

/-- The `m`-fold symmetrised set `symmUpTo_iso m A m` is invariant under coordinatewise
negation, obtained by chaining the `m` coordinate reflections. -/
theorem negFirst_mem_symmUpTo_iso (m : ℕ) (hC : SteinerCompactProp m) (hS : SteinerSymmProp m)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ symmUpTo_iso m A m) :
    ∀ k, k ≤ m → negFirst_iso m k x ∈ symmUpTo_iso m A m := by
  intro k
  induction k with
  | zero => intro _; rw [negFirst_zero_iso]; exact hx
  | succ k ih =>
      intro hk1
      have hkm : k < m := hk1
      have hstep := ih (le_of_lt hkm)
      rw [negFirst_succ_iso m k hkm x]
      exact reflE_mem_symmUpTo_iso m hC hS hA m ⟨k, hkm⟩ hkm (negFirst_iso m k x) hstep

theorem neg_mem_symmUpTo_iso (m : ℕ) (hC : SteinerCompactProp m) (hS : SteinerSymmProp m)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A) :
    ∀ x ∈ symmUpTo_iso m A m, -x ∈ symmUpTo_iso m A m := by
  intro x hx
  have h := negFirst_mem_symmUpTo_iso m hC hS hA hx m le_rfl
  rwa [negFirst_eq_neg_iso] at h

/-! ## Main theorem -/

/-- **Isodiametric inequality**, proved from the four Steiner symmetrisation properties. -/
theorem isodiametric_iso (m : ℕ) (hC : SteinerCompactProp m) (hV : SteinerVolumeProp m)
    (hD : SteinerDiamProp m) (hS : SteinerSymmProp m) : IsodiametricProp m := by
  intro A hA
  have hAstar_compact : IsCompact (symmUpTo_iso m A m) := isCompact_symmUpTo_iso m hC hA m
  have hAstar_vol : volume (symmUpTo_iso m A m) = volume A := volume_symmUpTo_iso m hC hV hA m
  have hAstar_diam : diam (symmUpTo_iso m A m) ≤ diam A := diam_symmUpTo_iso m hC hD hA m
  have hAstar_symm := neg_mem_symmUpTo_iso m hC hS hA
  have hsubset :
      symmUpTo_iso m A m ⊆ closedBall (0 : EuclideanSpace ℝ (Fin m)) (diam A / 2) := by
    intro x hx
    have hnx : -x ∈ symmUpTo_iso m A m := hAstar_symm x hx
    have hdd : dist x (-x) ≤ diam (symmUpTo_iso m A m) :=
      dist_le_diam_of_mem hAstar_compact.isBounded hx hnx
    have hdeq : dist x (-x) = 2 * ‖x‖ := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    have h2x : 2 * ‖x‖ ≤ diam A := hdeq ▸ hdd.trans hAstar_diam
    linarith
  calc volume A = volume (symmUpTo_iso m A m) := hAstar_vol.symm
    _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) (diam A / 2)) := measure_mono hsubset

end RobinCaps.Hausdorff

end
