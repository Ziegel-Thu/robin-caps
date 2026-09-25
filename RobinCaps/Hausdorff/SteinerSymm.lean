import RobinCaps.Hausdorff.IsodiamIface

/-!
# Symmetry properties of Steiner symmetrisation (wave 13, worker `SteinerSymm`)

This file proves `SteinerSymmProp m` from `RobinCaps.Hausdorff.IsodiamIface`: the Steiner
symmetrisation `steinerSym i A` of a set `A` in coordinate direction `i` is invariant under the
reflection `reflE i` in the `i`-th coordinate hyperplane, and it inherits invariance under any
other coordinate reflection `reflE j` (`j ≠ i`) that `A` itself already enjoys.

It also collects a handful of elementary coordinatewise facts about `reflE` (it is an involution,
two reflections in different coordinates commute, and applying all `m` coordinate reflections in
turn negates a point), culminating in `neg_mem_of_forall_reflE_sts`: a set that is invariant under
every single coordinate reflection is invariant under the central symmetry `x ↦ -x`. These
lemmas are recorded for a later worker finishing the isodiametric inequality.

All proofs are elementary and coordinatewise, via `PiLp.ext` and `Function.update_apply`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace RobinCaps.Hausdorff

variable {m : ℕ}

/-! ## Coordinatewise formulas for `updE` and `reflE` -/

/-- Coordinatewise formula for `updE`. -/
theorem updE_apply_sts (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) (t : ℝ) :
    (updE x i t) j = if j = i then t else x j := by
  unfold updE
  rw [PiLp.toLp_apply, Function.update_apply]

/-- Coordinatewise formula for `reflE`. -/
theorem reflE_apply_sts {i j : Fin m} {x : EuclideanSpace ℝ (Fin m)} :
    (reflE i x) j = if j = i then -(x i) else x j := by
  unfold reflE
  rw [updE_apply_sts]

/-- `reflE i` is an involution. -/
theorem reflE_reflE_sts (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    reflE i (reflE i x) = x := by
  apply PiLp.ext
  intro j
  rw [reflE_apply_sts]
  split_ifs with h
  · subst h
    rw [reflE_apply_sts]
    simp
  · rw [reflE_apply_sts]
    simp [h]

/-- Two coordinate reflections commute. -/
theorem reflE_comm_sts (i j : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    reflE i (reflE j x) = reflE j (reflE i x) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  apply PiLp.ext
  intro k
  rcases eq_or_ne k i with rfl | hki
  · simp [reflE_apply_sts, hij]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [reflE_apply_sts, hki]
    · simp [reflE_apply_sts, hki, hkj]

/-- Updating coordinate `i` after reflecting in that same coordinate has no effect: the value
that got reflected is immediately overwritten. -/
theorem updE_reflE_self_sts (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    updE (reflE i x) i t = updE x i t := by
  apply PiLp.ext
  intro k
  rw [updE_apply_sts, updE_apply_sts]
  split_ifs with h
  · rfl
  · rw [reflE_apply_sts]
    simp [h]

/-- Updating coordinate `i` commutes with reflecting in a different coordinate `j ≠ i`. -/
theorem updE_reflE_of_ne_sts (i j : Fin m) (hij : j ≠ i) (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    updE (reflE j x) i t = reflE j (updE x i t) := by
  apply PiLp.ext
  intro k
  rcases eq_or_ne k i with rfl | hki
  · simp [updE_apply_sts, reflE_apply_sts, hij.symm]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [updE_apply_sts, reflE_apply_sts, hki]
    · simp [updE_apply_sts, reflE_apply_sts, hki, hkj]

/-! ## Invariance of a `reflE`-invariant set -/

/-- If `A` is invariant under `reflE j`, then membership of `y` and of `reflE j y` in `A` agree. -/
theorem mem_reflE_iff_sts {j : Fin m} {A : Set (EuclideanSpace ℝ (Fin m))}
    (hA : ∀ x ∈ A, reflE j x ∈ A) (y : EuclideanSpace ℝ (Fin m)) :
    reflE j y ∈ A ↔ y ∈ A := by
  constructor
  · intro hy
    have := hA (reflE j y) hy
    rwa [reflE_reflE_sts] at this
  · intro hy
    exact hA y hy

/-- The fibre through `reflE i x` in direction `i` equals the fibre through `x`: reflecting in
the same coordinate the fibre is taken in has no effect on the fibre. -/
theorem fiberE_reflE_self_sts (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin m)) :
    fiberE i A (reflE i x) = fiberE i A x := by
  ext t
  simp only [fiberE, Set.mem_setOf_eq, updE_reflE_self_sts]

/-- If `A` is invariant under `reflE j` (`j ≠ i`), the fibre in direction `i` through `reflE j x`
equals the fibre through `x`. -/
theorem fiberE_reflE_of_ne_sts (i j : Fin m) (hij : j ≠ i) (A : Set (EuclideanSpace ℝ (Fin m)))
    (hA : ∀ x ∈ A, reflE j x ∈ A) (x : EuclideanSpace ℝ (Fin m)) :
    fiberE i A (reflE j x) = fiberE i A x := by
  ext t
  simp only [fiberE, Set.mem_setOf_eq, updE_reflE_of_ne_sts i j hij x t]
  exact mem_reflE_iff_sts hA _

/-- **Steiner symmetrisation is symmetric.** `steinerSym i A` is invariant under `reflE i`, and
it inherits invariance under any other coordinate reflection `reflE j` (`j ≠ i`) that `A` already
has. -/
theorem steinerSymm_sts (m : ℕ) : SteinerSymmProp m := by
  intro i A _hAcompact
  constructor
  · intro x hx
    obtain ⟨hne, hle⟩ := hx
    refine ⟨?_, ?_⟩
    · rwa [fiberE_reflE_self_sts]
    · have hi : (reflE i x) i = -(x i) := by rw [reflE_apply_sts]; simp
      rw [fiberE_reflE_self_sts, hi, abs_neg]
      exact hle
  · intro j hij hA x hx
    obtain ⟨hne, hle⟩ := hx
    have hij' : j ≠ i := hij
    refine ⟨?_, ?_⟩
    · rwa [fiberE_reflE_of_ne_sts i j hij' A hA]
    · have hi : (reflE j x) i = x i := by
        rw [reflE_apply_sts]
        simp [Ne.symm hij']
      rw [fiberE_reflE_of_ne_sts i j hij' A hA, hi]
      exact hle

/-! ## Negation via all coordinate reflections -/

/-- Folding `reflE` over a nodup list of coordinates negates exactly the coordinates in the
list, and leaves the others alone. -/
theorem foldr_reflE_apply_sts (l : List (Fin m)) (hl : l.Nodup) (x : EuclideanSpace ℝ (Fin m))
    (k : Fin m) :
    (l.foldr reflE x) k = if k ∈ l then -(x k) else x k := by
  induction l with
  | nil => simp
  | cons a l' ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨ha, hl'⟩ := hl
    rw [List.foldr_cons, reflE_apply_sts, ih hl']
    by_cases hka : k = a
    · subst hka
      have hnotmem : k ∉ l' := ha
      simp [ih hl', hnotmem]
    · have hka' : k ≠ a := hka
      by_cases hkl : k ∈ l' <;> simp [hka', hkl]

/-- Applying all `m` coordinate reflections in turn negates a point. -/
theorem neg_eq_foldr_reflE_sts (x : EuclideanSpace ℝ (Fin m)) :
    -x = (List.finRange m).foldr reflE x := by
  apply PiLp.ext
  intro k
  rw [foldr_reflE_apply_sts (List.finRange m) (List.nodup_finRange m) x k]
  simp [List.mem_finRange]

/-- Folding `reflE` over any list, starting from a point in a `reflE`-invariant set `S`, stays
in `S`. -/
theorem foldr_reflE_mem_sts {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : ∀ i, ∀ x ∈ S, reflE i x ∈ S) (l : List (Fin m)) (x : EuclideanSpace ℝ (Fin m))
    (hx : x ∈ S) :
    l.foldr reflE x ∈ S := by
  induction l with
  | nil => simpa using hx
  | cons a l' ih => rw [List.foldr_cons]; exact hS a _ ih

/-- A set invariant under every single coordinate reflection is invariant under the central
symmetry `x ↦ -x`. -/
theorem neg_mem_of_forall_reflE_sts {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : ∀ i, ∀ x ∈ S, reflE i x ∈ S) : ∀ x ∈ S, -x ∈ S := by
  intro x hx
  rw [neg_eq_foldr_reflE_sts]
  exact foldr_reflE_mem_sts hS (List.finRange m) x hx

end RobinCaps.Hausdorff

end
